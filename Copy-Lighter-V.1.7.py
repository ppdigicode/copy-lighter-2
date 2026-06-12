#!/usr/bin/env python3
"""
Lighter Copy Trading Bot - Educational Example

⚠️  WARNING: This bot trades with REAL money on MAINNET
    - Always test in DRY_RUN mode first
    - Never share your private keys
    - You can lose money - use at your own risk
    - Not financial advice
"""

import os
import sys
import json
import signal
import math
import time
import datetime
import threading
import asyncio
from queue import Queue
from concurrent.futures import ThreadPoolExecutor
from decimal import Decimal
from dotenv import load_dotenv
import websockets

# Lighter official SDK
import lighter


class CopyTradingBot:
    """
    Copy trading bot that listens to a target user's fills and mirrors them
    """

    def __init__(self):
        print("\n🤖 Lighter Copy Trading Bot v0.9")

        load_dotenv()

        # === Configuration ===
        self.base_url = os.getenv('LIGHTER_BASE_URL', 'https://mainnet.zklighter.elliot.ai')
        self.ws_url = os.getenv('LIGHTER_WS_URL', 'wss://mainnet.zklighter.elliot.ai/stream')
        
        self.target_account_index = int(os.getenv('TARGET_ACCOUNT_INDEX', '0'))
        self.copy_percentage = float(os.getenv('COPY_PERCENTAGE', '5.0'))
        self.dry_run = os.getenv('DRY_RUN', 'true').lower() == 'true'
        self.max_position_usd = float(os.getenv('MAX_POSITION_SIZE_USD', '100'))
        self.min_position_usd = float(os.getenv('MIN_POSITION_SIZE_USD', '10'))
        self.max_open_positions = int(os.getenv('MAX_OPEN_POSITIONS', '4'))
        self.slippage_tolerance_pct = float(os.getenv('SLIPPAGE_TOLERANCE_PCT', '0.5'))
        self.min_notional_usd = 10.0  # Lighter exchange minimum

        # Coin filtering mode
        self.coin_filter_mode = os.getenv('COIN_FILTER_MODE', 'ALL').upper()  # ALL or ENABLED
        enabled_coins_str = os.getenv('ENABLED_COINS', '').strip()
        self.enabled_coins = set(c.strip() for c in enabled_coins_str.split(',')) if enabled_coins_str else None

        # Credentials for live trading
        self.api_key_index = int(os.getenv('API_KEY_INDEX', '3'))
        self.api_private_key = os.getenv('API_PRIVATE_KEY', '')
        self.our_account_index = int(os.getenv('OUR_ACCOUNT_INDEX', '0')) if not self.dry_run else None

        # Safety / reconnect config
        self.reconnect_delay_sec = float(os.getenv("RECONNECT_DELAY_SEC", "2.0"))
        safety_flatten = os.getenv("SAFETY_FLATTEN_AFTER_SEC", "").strip()
        self.safety_flatten_after_sec = float(safety_flatten) if safety_flatten else None
        self.disconnect_start_time = None

        # ---- Coalescing ----
        self.coalesce_window_ms = int(os.getenv("COALESCE_WINDOW_MS", "100"))
        self._coalesce_buf = {}  # key -> {sum_sz, sum_px_sz, max_time, first_ms, last_ms, template_fill}
        self._agg_counter = 0

        # ---- Periodic flusher thread ----
        self.coalesce_flush_interval_ms = int(os.getenv("COALESCE_FLUSH_INTERVAL_MS", "25"))
        self.coalesce_lock = threading.Lock()
        self.coalesce_flusher_thread = None

        # === State Tracking ===
        self.processed_fills = set()      # Avoid duplicate fills (TARGET only; includes aggregated ids)
        self.open_positions = {}          # {market_index: net size} - positive=long, negative=short (OUR ACCOUNT)
        self.open_positions_est = {}      # {market_index: net size} optimistic/estimated
        self.market_metadata = {}         # Cached metadata per market
        self.target_positions = {}        # {market_index: net size} - target trader reconstructed

        # ---- Pending closes + sync-on-miss rate limit ----
        self.pending_closes = {}          # {market_index: [ {frac, price, dir, ts_ms}, ... ]}
        self.last_sync_ts = {}            # {market_index: last_sync_time_sec}
        self.sync_on_miss_cooldown_sec = float(os.getenv("SYNC_ON_MISS_COOLDOWN_SEC", "0.5"))
        
        # ---- Order latency tracking ----
        self.order_target_timestamps = {}  # {market_index: target_fill_timestamp_ms} - for latency calculation
        
        # ---- Order placement lock (prevent nonce conflicts) ----
        self.order_lock = threading.Lock()

        # ---- Periodic target state reconciliation ----
        self.target_state_sync_interval_sec = float(os.getenv("TARGET_STATE_SYNC_INTERVAL_SEC", "2.0"))
        self.orphan_close_cooldown_sec = float(os.getenv("ORPHAN_CLOSE_COOLDOWN_SEC", "1.0"))
        self.target_positions_actual = {}   # {market_index: net size} from API
        self.last_orphan_close_ts = {}      # {market_index: last_attempt_time_sec}
        self.target_state_thread = None

        # === Async pipeline ===
        self.state_lock = threading.Lock()
        self.main_loop = None  # Will be set in _run_async
        self.stop_event = threading.Event()
        self.fill_queue_max = int(os.getenv('FILL_QUEUE_MAX', '5000'))
        self.order_workers = int(os.getenv('ORDER_WORKERS', '4'))
        self.fill_queue = Queue(maxsize=self.fill_queue_max)
        self.exec_pool = None
        self.dispatcher_thread = None
        self.dropped_fills = 0

        signal.signal(signal.SIGINT, self._signal_handler)

        # Basic checks
        if self.target_account_index == 0:
            print("\n❌ ERROR: TARGET_ACCOUNT_INDEX not set in .env\n")
            sys.exit(1)

        if not self.dry_run:
            if not self.api_private_key or self.our_account_index == 0:
                print("\n❌ ERROR: Live mode requires API_PRIVATE_KEY and OUR_ACCOUNT_INDEX in .env\n")
                sys.exit(1)

        # === Initialize Lighter SDK ===
        self.api_client = None
        self.signer_client = None
        self.account_api = None
        self.order_api = None
        # SDK will be initialized in run() to keep event loop alive

        print(f"\n🎯 Copying trades from account: {self.target_account_index}")
        print(f"📊 Copy percentage: {self.copy_percentage}%")
        print(f"🧪 Dry run mode: {self.dry_run}")
        if self.coin_filter_mode == 'ENABLED':
            print(f"🧩 Coin filter: ENABLED (allowed: {sorted(self.enabled_coins) if self.enabled_coins else []})")
        else:
            print("🧩 Coin filter: ALL")
        print(f"📌 Max open positions: {self.max_open_positions}")
        print(f"📉 Slippage tolerance: {self.slippage_tolerance_pct}%")
        print(f"⛔ Min notional per order: ${self.min_notional_usd:.2f}")
        print(f"🧮 Coalesce window: {self.coalesce_window_ms}ms\n")

        # Metadata and positions will be synced after SDK initialization in run()

    # ------------------------
    # SDK Initialization
    # ------------------------
    async def _initialize_lighter_sdk(self):
        """Initialize Lighter SDK (must be called in async context)"""
        try:
            print("🔧 Initializing Lighter SDK...")
            
            # Initialize API client for read operations
            self.api_client = lighter.ApiClient(lighter.Configuration(host=self.base_url))
            print("✅ API client initialized")
            
            # Initialize signer client for transactions
            print(f"🔧 Creating SignerClient (account_index={self.our_account_index}, api_key_index={self.api_key_index})...")
            self.signer_client = lighter.SignerClient(
                url=self.base_url,
                api_private_keys={self.api_key_index: self.api_private_key},
                account_index=self.our_account_index
            )
            
            if self.signer_client is None:
                print("❌ ERROR: SignerClient initialization returned None")
                sys.exit(1)
            
            print("✅ SignerClient created")
            
            # Check that signer client is properly configured - synchronous method
            print("🔧 Checking signer client configuration...")
            err = self.signer_client.check_client()
            if err:
                print(f"❌ ERROR: Signer client check failed: {err}")
                sys.exit(1)
            
            print("✅ Signer client check passed")
            
            # Initialize API instances
            self.account_api = lighter.AccountApi(self.api_client)
            self.order_api = lighter.OrderApi(self.api_client)

            # Fetch account info
            account_info = await self.account_api.account(by="index", value=str(self.our_account_index))
            if account_info and hasattr(account_info, 'collateral'):
                print(f"💰 Account collateral: ${float(account_info.collateral):.2f}")
                
        except Exception as e:
            print(f"❌ ERROR: Failed to initialize Lighter SDK: {e}")
            import traceback
            traceback.print_exc()
            sys.exit(1)

    # ------------------------
    # Async pipeline (target fills)
    # ------------------------
    def _start_async_pipeline(self):
        if self.exec_pool is not None:
            return
        self.exec_pool = ThreadPoolExecutor(max_workers=max(1, self.order_workers))
        self.dispatcher_thread = threading.Thread(target=self._dispatcher_loop, name="fill-dispatcher", daemon=True)
        self.dispatcher_thread.start()

        # Start periodic flusher
        if self.coalesce_flusher_thread is None:
            self.coalesce_flusher_thread = threading.Thread(
                target=self._coalesce_flusher_loop,
                name="coalesce-flusher",
                daemon=True
            )
            self.coalesce_flusher_thread.start()

        # Start periodic target-state reconciliation thread
        if self.target_state_thread is None and self.target_state_sync_interval_sec > 0:
            self.target_state_thread = threading.Thread(
                target=self._target_state_sync_loop,
                name="target-state-sync",
                daemon=True
            )
            self.target_state_thread.start()

    def _dispatcher_loop(self):
        while not self.stop_event.is_set():
            try:
                fill = self.fill_queue.get(timeout=1)
                if fill is None:
                    break
                self.exec_pool.submit(self._process_target_fill, fill)
            except Exception:
                pass

    def _coalesce_flusher_loop(self):
        while not self.stop_event.is_set():
            time.sleep(self.coalesce_flush_interval_ms / 1000.0)
            try:
                now_ms = int(time.time() * 1000)
                self._coalesce_flush_due(now_ms)
            except Exception as e:
                pass

    def _target_state_sync_loop(self):
        while not self.stop_event.is_set():
            time.sleep(self.target_state_sync_interval_sec)
            try:
                self._sync_target_actual_positions()
                self._check_orphan_positions()
            except Exception as e:
                pass

    # ------------------------
    # Metadata
    # ------------------------
    async def _fetch_market_metadata_async(self):
        """Fetch market metadata from Lighter (async version)"""
        if not self.order_api:
            return
        
        try:
            order_books = await self.order_api.order_books()
            if order_books and hasattr(order_books, 'order_books'):
                for ob in order_books.order_books:
                    market_index = ob.market_id
                    
                    metadata = {
                        'symbol': ob.symbol,
                        # CRITICAL: Use 'supported_*' fields, not the deprecated ones
                        'size_decimals': getattr(ob, 'supported_size_decimals', 4),
                        'price_decimals': getattr(ob, 'supported_price_decimals', 2),
                        'min_size': getattr(ob, 'min_size', '0.001'),
                    }
                    
                    # Try to get min_base_amount or other min limits
                    for attr in ['min_base_amount', 'min_quote_amount', 'min_order_size', 'min_notional', 'quote_decimals']:
                        if hasattr(ob, attr):
                            val = getattr(ob, attr)
                            metadata[attr] = val
                    
                    self.market_metadata[market_index] = metadata
                    
                print(f"✅ Loaded metadata for {len(self.market_metadata)} markets")
                        
        except Exception as e:
            print(f"⚠️  Error fetching market metadata: {e}")

    def _fetch_market_metadata(self):
        """Fetch market metadata from Lighter"""
        if self.dry_run or not self.order_api:
            return
        
        # Skip if no event loop (will be called again later)
        try:
            loop = asyncio.get_event_loop()
            if loop.is_closed():
                return
        except RuntimeError:
            return
        
        try:
            order_books = asyncio.run(self.order_api.order_books())
            if order_books and hasattr(order_books, 'order_books'):
                for ob in order_books.order_books:
                    market_index = ob.market_id
                    self.market_metadata[market_index] = {
                        'symbol': ob.symbol,
                        'size_decimals': getattr(ob, 'size_decimals', 4),
                        'price_decimals': getattr(ob, 'price_decimals', 2),
                        'min_size': getattr(ob, 'min_size', '0.001')
                    }
                print(f"✅ Loaded metadata for {len(self.market_metadata)} markets")
        except Exception as e:
            print(f"⚠️  Error fetching market metadata: {e}")

    # ------------------------
    # Metadata helpers
    # ------------------------

    def _get_market_symbol(self, market_index):
        """Get symbol for market"""
        if market_index in self.market_metadata:
            return self.market_metadata[market_index].get('symbol', f'MARKET_{market_index}')
        return f'MARKET_{market_index}'

    def _round_size(self, market_index, size):
        """Round size to market precision"""
        if market_index not in self.market_metadata:
            return round(size, 4)
        decimals = self.market_metadata[market_index].get('size_decimals', 4)
        return round(size, decimals)

    def _round_price(self, market_index, price):
        """Round price to market precision"""
        if market_index not in self.market_metadata:
            return round(price, 2)
        decimals = self.market_metadata[market_index].get('price_decimals', 2)
        return round(price, decimals)

    # ------------------------
    # Position sync
    # ------------------------
    async def _sync_positions_from_exchange_async(self, verbose=False, update_estimated=True):
        """Sync our actual positions from exchange (async version)"""
        if not self.account_api:
            return

        try:
            account = await self.account_api.account(by="index", value=str(self.our_account_index))
            
            new_positions = {}
            if account and hasattr(account, 'positions'):
                for pos in account.positions:
                    market_index = pos.market_id
                    position_size = float(pos.position or 0)
                    sign = getattr(pos, 'sign', 1)
                    net_size = position_size * sign
                    
                    if abs(net_size) > 1e-8:
                        new_positions[market_index] = net_size

            with self.state_lock:
                self.open_positions = new_positions
                if update_estimated:
                    self.open_positions_est = dict(new_positions)

            if verbose:
                if new_positions:
                    print(f"📊 Current positions:")
                    for market_index, size in new_positions.items():
                        symbol = self._get_market_symbol(market_index)
                        print(f"   {symbol}: {size:+.4f}")
                else:
                    print("📊 No open positions")

        except Exception as e:
            print(f"⚠️  Error syncing positions: {e}")

    def _sync_positions_from_exchange(self, verbose=False, update_estimated=True):
        """Sync our actual positions from exchange (wrapper for thread)"""
        if self.dry_run or not self.account_api or not self.main_loop:
            return

        try:
            if self.main_loop and self.main_loop.is_running():
                future = asyncio.run_coroutine_threadsafe(
                    self._sync_positions_from_exchange_async(verbose, update_estimated),
                    self.main_loop
                )
                future.result(timeout=5)
        except Exception as e:
            print(f"⚠️  Error syncing positions: {e}")

    async def _sync_target_actual_positions_async(self):
        """Sync target trader's actual positions (async version)"""
        if not self.account_api:
            return

        try:
            response = await self.account_api.account(by="index", value=str(self.target_account_index))
            
            new_target_positions = {}
            
            # The response is DetailedAccounts with an 'accounts' list
            if response and hasattr(response, 'accounts') and len(response.accounts) > 0:
                account = response.accounts[0]  # Get first account from list
                
                if hasattr(account, 'positions'):
                    for pos in account.positions:
                        market_index = pos.market_id
                        position_size = float(pos.position or 0)
                        sign = getattr(pos, 'sign', 1)
                        net_size = position_size * sign
                        
                        if abs(net_size) > 1e-8:
                            new_target_positions[market_index] = net_size

            with self.state_lock:
                self.target_positions_actual = new_target_positions

        except Exception as e:
            if not self.stop_event.is_set():
                print(f"⚠️  Error syncing target positions from API: {type(e).__name__}: {e}")

    def _sync_target_actual_positions(self):
        """Sync target trader's actual positions (wrapper for thread)"""
        if self.stop_event.is_set():
            return
        
        if not self.account_api or not self.main_loop:
            return

        try:
            if self.main_loop and self.main_loop.is_running():
                future = asyncio.run_coroutine_threadsafe(
                    self._sync_target_actual_positions_async(),
                    self.main_loop
                )
                future.result(timeout=5)  # Wait max 5 seconds
        except Exception as e:
            if not self.stop_event.is_set():  # Only log if not shutting down
                print(f"⚠️  Error in target position sync: {e}")
                import traceback
                traceback.print_exc()

    def _check_orphan_positions(self):
        """Check for orphan positions (we have position but target is flat)"""
        if self.stop_event.is_set() or self.dry_run:
            return

        with self.state_lock:
            target_actual = dict(self.target_positions_actual)
            our_pos = dict(self.open_positions)

        now = time.time()
        for market_index, our_size in our_pos.items():
            if abs(our_size) < 1e-8:
                continue

            target_size = target_actual.get(market_index, 0.0)
            if abs(target_size) < 1e-8:
                # Target is flat but we have position - orphan detected
                last_close = self.last_orphan_close_ts.get(market_index, 0)
                if now - last_close < self.orphan_close_cooldown_sec:
                    continue

                symbol = self._get_market_symbol(market_index)
                print(f"🔍 Orphan position detected: {symbol} (our: {our_size:+.4f}, target: 0)")
                
                self.last_orphan_close_ts[market_index] = now
                
                # Close orphan position
                try:
                    is_buy = our_size < 0
                    size = abs(our_size)
                    
                    # Get market price
                    price = self._get_market_price(market_index, is_buy)
                    if not price:
                        print(f"   ⚠️  Could not get market price for orphan close, will retry in {self.orphan_close_cooldown_sec}s")
                        # Reset cooldown so we retry sooner
                        self.last_orphan_close_ts[market_index] = now - self.orphan_close_cooldown_sec + 0.5
                        continue
                    
                    print(f"   🧹 Closing orphan: {'BUY' if is_buy else 'SELL'} {size:.4f} {symbol} @ ${price:.4f}")
                    self._place_order_internal(market_index, is_buy, size, price, is_closing=True)
                except Exception as e:
                    print(f"❌ Failed to close orphan position {symbol}: {e}")
                    import traceback
                    traceback.print_exc()

    # ------------------------
    # Coalescing
    # ------------------------
    def _coalesce_add_fill(self, fill_dict):
        """Add fill to coalescing buffer"""
        market_index = fill_dict.get('market_id')
        if market_index is None:
            return

        ask_account_id = fill_dict.get('ask_account_id')
        bid_account_id = fill_dict.get('bid_account_id')
        
        # Determine if this is our target account
        if ask_account_id == self.target_account_index:
            side = 'SELL'
        elif bid_account_id == self.target_account_index:
            side = 'BUY'
        else:
            return

        recv_ms = fill_dict.get('_recv_ms', int(time.time() * 1000))
        
        with self.coalesce_lock:
            key = (market_index, side)
            
            if key not in self._coalesce_buf:
                self._coalesce_buf[key] = {
                    'sum_sz': 0.0,
                    'sum_px_sz': 0.0,
                    'max_time': recv_ms,
                    'first_ms': recv_ms,
                    'last_ms': recv_ms,
                    'template_fill': fill_dict
                }

            buf = self._coalesce_buf[key]
            size = float(fill_dict.get('size', 0))
            price = float(fill_dict.get('price', 0))
            
            buf['sum_sz'] += size
            buf['sum_px_sz'] += price * size
            buf['last_ms'] = recv_ms
            buf['max_time'] = max(buf['max_time'], recv_ms)

    def _coalesce_flush_due(self, now_ms):
        """Flush coalesced fills that are ready"""
        to_flush = []
        
        with self.coalesce_lock:
            for key, buf in list(self._coalesce_buf.items()):
                age_ms = now_ms - buf['first_ms']
                if age_ms >= self.coalesce_window_ms:
                    to_flush.append((key, buf))
                    del self._coalesce_buf[key]

        for key, buf in to_flush:
            self._emit_aggregated_fill(key, buf)

    def _coalesce_flush_all(self):
        """Flush all coalesced fills immediately"""
        with self.coalesce_lock:
            items = list(self._coalesce_buf.items())
            self._coalesce_buf.clear()

        for key, buf in items:
            self._emit_aggregated_fill(key, buf)

    def _emit_aggregated_fill(self, key, buf):
        """Emit aggregated fill to processing queue"""
        self._agg_counter += 1
        agg_id = f"agg_{self._agg_counter}"

        market_index, side = key
        avg_price = buf['sum_px_sz'] / buf['sum_sz'] if buf['sum_sz'] > 0 else 0
        
        agg_fill = {
            'trade_id': agg_id,
            'market_id': market_index,
            'size': str(buf['sum_sz']),
            'price': str(avg_price),
            'side': side,
            'timestamp': buf['max_time'],
            '_is_aggregated': True,
            '_recv_ms': buf['first_ms']
        }

        try:
            self.fill_queue.put_nowait(agg_fill)
        except:
            self.dropped_fills += 1

    # ------------------------
    # Fill processing
    # ------------------------
    def _process_target_fill(self, fill):
        """Process a target trader fill"""
        try:
            trade_id = fill.get('trade_id')
            
            # Check if already processed
            with self.state_lock:
                if trade_id in self.processed_fills:
                    return
                self.processed_fills.add(trade_id)

            market_index = fill.get('market_id')
            if market_index is None:
                return

            symbol = self._get_market_symbol(market_index)
            
            # Check coin filter
            if self.coin_filter_mode == 'ENABLED':
                if self.enabled_coins and symbol not in self.enabled_coins:
                    return

            size = float(fill.get('size', 0))
            price = float(fill.get('price', 0))
            
            if price == 0:
                return
            side = fill.get('side', 'UNKNOWN')
            
            recv_ms = fill.get('_recv_ms', int(time.time() * 1000))
            event_ms = int(fill.get('timestamp', 0))
            latency_ms = recv_ms - event_ms if event_ms > 0 else None

            is_buy = side == 'BUY'
            is_sell = side == 'SELL'

            if not is_buy and not is_sell:
                return

            # CRITICAL: Update target position FIRST, before any filters
            # This ensures we track target's position even if we skip placing our order
            with self.state_lock:
                current_target = self.target_positions.get(market_index, 0.0)
                delta = size if is_buy else -size
                new_target = current_target + delta
                self.target_positions[market_index] = new_target
            
            # Now current_target has the OLD position (before this fill)
            # new_target has the NEW position (after this fill)
            
            # Determine if this is a closing trade EARLY
            # A trade is a close if it reduces the target's position
            is_closing = False
            if is_buy and current_target < 0:  # Buying to close short
                is_closing = True
            elif is_sell and current_target > 0:  # Selling to close long
                is_closing = True

            # Calculate our order size
            our_size = size * (self.copy_percentage / 100.0)
            our_size = self._round_size(market_index, our_size)
            
            # Calculate notional
            notional = our_size * price

            # Check min notional ONLY for OPENS (not closes)
            if not is_closing:
                if notional < self.min_notional_usd:
                    return

            # Check max position (only for OPENS)
            if not is_closing and notional > self.max_position_usd:
                our_size = self.max_position_usd / price
                our_size = self._round_size(market_index, our_size)

            # Check max open positions
            with self.state_lock:
                num_open = sum(1 for s in self.open_positions_est.values() if abs(s) > 1e-8)
                our_pos = self.open_positions_est.get(market_index, 0.0)
                
                if abs(our_pos) < 1e-8 and num_open >= self.max_open_positions:
                    print(f"⚠️  Max positions ({self.max_open_positions}) reached, skipping {symbol}")
                    return

            # Get price decimals for display
            market_meta = self.market_metadata.get(market_index, {})
            price_decimals = market_meta.get('price_decimals', 2)
            
            # Calculate metrics like Hyperliquid
            now_ms = int(time.time() * 1000)
            
            # Exchange lag (time from event to now)
            exchange_lag_ms = now_ms - event_ms if event_ms > 0 else None
            
            # WS receive lag (time from event to WS receipt)
            ws_recv_lag_ms = recv_ms - event_ms if event_ms > 0 else None
            
            # Queue lag (time from receipt to processing)
            queue_lag_ms = now_ms - recv_ms if recv_ms > 0 else None
            
            # Get queue size
            try:
                qsize = self.fill_queue.qsize()
            except:
                qsize = -1
            
            # Format timestamp
            tstamp_str = ""
            if event_ms > 0:
                try:
                    import datetime
                    dt = datetime.datetime.fromtimestamp(event_ms / 1000.0)
                    tstamp_str = dt.strftime("%H:%M:%S")
                except:
                    tstamp_str = ""
            
            # is_closing is already determined above
            action = "CLOSE" if is_closing else "OPEN"
            side_name = 'BUY' if is_buy else 'SELL'
            notional = size * price  # Use target's size for notional
            
            # Build lag parts
            lag_parts = []
            if exchange_lag_ms is not None:
                lag_parts.append(f"exchange_lag={exchange_lag_ms}ms")
            if ws_recv_lag_ms is not None:
                lag_parts.append(f"ws_recv_lag={ws_recv_lag_ms}ms")
            if queue_lag_ms is not None:
                lag_parts.append(f"queue_lag={queue_lag_ms}ms")
            lag_parts.append(f"queue_size={qsize}")
            
            # Print detailed logs like Hyperliquid
            print("\n" + "=" * 70)
            print(f"📩 {tstamp_str} Target {action}: {side_name} {size:.4f} {symbol} @ ${price:.{price_decimals}f} (${notional:.2f}) | {', '.join(lag_parts)}")
            
            # Handle CLOSE logic with fraction
            if is_closing:
                with self.state_lock:
                    prev_target_pos = current_target  # Already loaded above
                
                target_close_sz = size
                frac = (target_close_sz / abs(prev_target_pos)) if abs(prev_target_pos) > 0 else 1.0
                
                with self.state_lock:
                    has_pos = (market_index in self.open_positions)
                    # Use estimated position with fallback to real position (like Hyperliquid)
                    our_pos = float(self.open_positions_est.get(market_index, self.open_positions.get(market_index, 0.0)))
                
                # If we don't have a real position tracked yet, sync from API
                if not has_pos:
                    self._sync_positions_from_exchange(verbose=False, update_estimated=False)
                    
                    with self.state_lock:
                        has_pos2 = (market_index in self.open_positions)
                        our_pos2 = float(self.open_positions.get(market_index, 0.0))
                    
                    if not has_pos2:
                        # Still no position - skip
                        print("=" * 70)
                        return
                    
                    our_pos = our_pos2
                
                # Use estimated position for close size (like Hyperliquid)
                our_pos_est = self.open_positions_est.get(market_index, our_pos)
                our_close_sz = self._round_size(market_index, abs(our_pos_est) * frac)
                
                if our_close_sz <= 0:
                    print("=" * 70)
                    return
                
                frac_pct = frac * 100
                print(f"   📉 Target close: {frac_pct:.1f}% of their position")
                print(f"   📉 Our close: {our_close_sz:.4f} (from our est pos {abs(our_pos_est):.4f})")
                
                # Place close order
                self._place_order_internal(market_index, is_buy, our_close_sz, price, is_closing=True, target_fill_time_ms=event_ms)
                print("=" * 70)
                return
            
            # OPEN logic (not a close)
            # Place our order
            self._place_order_internal(market_index, is_buy, our_size, price, is_closing=False, target_fill_time_ms=event_ms)
            print("=" * 70)

        except Exception as e:
            print(f"❌ Error processing fill: {e}")

    def _place_order_internal(self, market_index, is_buy, size, price, is_closing=False, target_fill_time_ms=None):
        """Place an order on Lighter"""
        symbol = self._get_market_symbol(market_index)
        side_str = 'BUY' if is_buy else 'SELL'

        # Adjust price for slippage
        if is_buy:
            price = price * (1 + self.slippage_tolerance_pct / 100.0)
        else:
            price = price * (1 - self.slippage_tolerance_pct / 100.0)
        
        price = self._round_price(market_index, price)
        size = self._round_size(market_index, size)

        # Update estimated position
        with self.state_lock:
            current = self.open_positions_est.get(market_index, 0.0)
            delta = size if is_buy else -size
            new_est = current + delta
            
            # CRITICAL: If this is a reduce-only close, never let the estimate flip sign past zero
            # This prevents accidentally opening a position in the opposite direction
            if is_closing:
                if current > 0 and new_est < 0:
                    new_est = 0.0
                elif current < 0 and new_est > 0:
                    new_est = 0.0
            
            self.open_positions_est[market_index] = new_est
            
            # Store target fill timestamp for latency calculation
            if target_fill_time_ms:
                self.order_target_timestamps[market_index] = target_fill_time_ms

        if self.dry_run:
            print(f"🧪 DRY RUN: Would {side_str} {size:.4f} {symbol} @ ${price:.2f}")
            return

        if not self.signer_client:
            print(f"❌ ERROR: SignerClient not initialized, cannot place order")
            # Revert estimated position
            with self.state_lock:
                current = self.open_positions_est.get(market_index, 0.0)
                delta = size if is_buy else -size
                self.open_positions_est[market_index] = current - delta
            return

        # Use run_coroutine_threadsafe to submit to main event loop
        try:
            if self.main_loop and self.main_loop.is_running():
                # Submit coroutine to main loop from worker thread
                future = asyncio.run_coroutine_threadsafe(
                    self._place_order_async(market_index, is_buy, size, price, is_closing, symbol, side_str),
                    self.main_loop
                )
                # Wait for result with timeout
                future.result(timeout=10)
            else:
                print(f"❌ ERROR: Main event loop not available")
                # Revert estimated position
                with self.state_lock:
                    current = self.open_positions_est.get(market_index, 0.0)
                    delta = size if is_buy else -size
                    self.open_positions_est[market_index] = current - delta
        except Exception as e:
            print(f"❌ Order failed: {e}")
            # Revert estimated position
            with self.state_lock:
                current = self.open_positions_est.get(market_index, 0.0)
                delta = size if is_buy else -size
                self.open_positions_est[market_index] = current - delta

    async def _place_order_async(self, market_index, is_buy, size, price, is_closing, symbol, side_str):
        """Async wrapper for placing orders"""
        try:
            # Get market metadata for proper decimal conversion
            market_meta = self.market_metadata.get(market_index, {})
            
            size_decimals = market_meta.get('size_decimals', 4)
            price_decimals = market_meta.get('price_decimals', 2)
            min_size = float(market_meta.get('min_size', '0.001'))
            
            # Check minimum size
            if size < min_size:
                print(f"⏭️  Size {size:.6f} below minimum {min_size:.6f}, skipping")
                # Revert estimated position
                with self.state_lock:
                    current = self.open_positions_est.get(market_index, 0.0)
                    delta = size if is_buy else -size
                    self.open_positions_est[market_index] = current - delta
                return
            
            print(f"📤 Placing order: {side_str} {size:.4f} {symbol} @ ${price:.{price_decimals}f}")
            
            # Convert to Lighter format
            base_amount = round(size * (10 ** size_decimals))
            limit_price = round(price * (10 ** price_decimals))
            
            # Check minimum base_amount from market metadata (only for OPENS)
            if not is_closing:
                min_base_amount_raw = market_meta.get('min_base_amount', 0)
                try:
                    min_base_amount = int(float(min_base_amount_raw)) if min_base_amount_raw else 0
                except (ValueError, TypeError):
                    min_base_amount = 0
                
                # Only enforce minimum if metadata explicitly specifies one
                if min_base_amount > 0 and base_amount < min_base_amount:
                    print(f"⚠️  Order too small: base_amount={base_amount} < min={min_base_amount} (from metadata)")
                    print(f"   (size={size:.4f} * 10^{size_decimals} = {base_amount})")
                    # Revert estimated position
                    with self.state_lock:
                        current = self.open_positions_est.get(market_index, 0.0)
                        delta = size if is_buy else -size
                        self.open_positions_est[market_index] = current - delta
                    return
            
            # CRITICAL: Serialize order placement to avoid nonce conflicts
            # When multiple fills arrive simultaneously, we need to place orders sequentially
            # to prevent "invalid nonce" errors from Lighter exchange
            loop = asyncio.get_event_loop()
            
            async def _create_order_with_lock():
                # Acquire lock in a thread-safe way
                await loop.run_in_executor(None, self.order_lock.acquire)
                try:
                    result = await self.signer_client.create_order(
                        market_index=market_index,
                        is_ask=not is_buy,
                        base_amount=base_amount,
                        price=limit_price,
                        order_type=self.signer_client.ORDER_TYPE_LIMIT,
                        time_in_force=self.signer_client.ORDER_TIME_IN_FORCE_GOOD_TILL_TIME,
                        reduce_only=is_closing,
                        client_order_index=0
                    )
                    return result
                finally:
                    self.order_lock.release()
            
            result = await _create_order_with_lock()
            
            # result is a tuple: (tx, tx_hash, error)
            tx, tx_hash, err = result
            
            if err:
                print(f"⚠️  Order placement error: {err}")
                # Revert estimated position
                with self.state_lock:
                    current = self.open_positions_est.get(market_index, 0.0)
                    delta = size if is_buy else -size
                    self.open_positions_est[market_index] = current - delta
            else:
                print(f"✅ Order placed successfully")

        except Exception as e:
            print(f"❌ Order failed: {e}")
            # Revert estimated position
            with self.state_lock:
                current = self.open_positions_est.get(market_index, 0.0)
                delta = size if is_buy else -size
                self.open_positions_est[market_index] = current - delta

    async def _get_market_price_async(self, market_index, is_buy):
        """Get current market price for a market (async version)"""
        try:
            order_book_response = await self.order_api.order_book_details(market_id=str(market_index))
            
            if not order_book_response:
                return None
            
            # The response wraps the actual order book
            if hasattr(order_book_response, 'order_book_details'):
                order_book = order_book_response.order_book_details
            elif hasattr(order_book_response, 'spot_order_book_details'):
                order_book = order_book_response.spot_order_book_details
            else:
                return None
            
            if not order_book:
                return None
            
            if is_buy:
                if hasattr(order_book, 'asks') and order_book.asks:
                    return float(order_book.asks[0].price)
                return None
            else:
                if hasattr(order_book, 'bids') and order_book.bids:
                    return float(order_book.bids[0].price)
                return None
                
        except Exception:
            pass
        return None
    
    def _get_market_price(self, market_index, is_buy):
        """Get current market price for a market (wrapper for thread)"""
        if not self.order_api or not self.main_loop:
            return None
        
        try:
            if self.main_loop and self.main_loop.is_running():
                future = asyncio.run_coroutine_threadsafe(
                    self._get_market_price_async(market_index, is_buy),
                    self.main_loop
                )
                return future.result(timeout=5)
        except Exception as e:
            print(f"⚠️  Error in market price wrapper: {e}")
        return None

    def _apply_our_fill_to_positions(self, fill):
        """Update our position tracking when we get filled"""
        try:
            market_index = fill.get('market_id')
            if market_index is None:
                return

            size = float(fill.get('size', 0))
            price = float(fill.get('price', 0))
            ask_account_id = fill.get('ask_account_id')
            bid_account_id = fill.get('bid_account_id')

            if ask_account_id == self.our_account_index:
                delta = -size
            elif bid_account_id == self.our_account_index:
                delta = size
            else:
                return

            with self.state_lock:
                current = self.open_positions.get(market_index, 0.0)
                new_pos = current + delta
                
                # Clean up positions very close to zero
                if abs(new_pos) < 1e-8:
                    self.open_positions.pop(market_index, None)
                    self.open_positions_est.pop(market_index, None)
                else:
                    self.open_positions[market_index] = new_pos
                    self.open_positions_est[market_index] = new_pos
                
                # Get target fill timestamp for latency calculation
                target_fill_ts = self.order_target_timestamps.pop(market_index, None)

            symbol = self._get_market_symbol(market_index)
            side = 'BUY' if delta > 0 else 'SELL'
            
            # Get price decimals for display
            market_meta = self.market_metadata.get(market_index, {})
            price_decimals = market_meta.get('price_decimals', 2)
            
            # Calculate latency if we have the target timestamp
            latency_str = ""
            if target_fill_ts:
                our_fill_ts = int(fill.get('timestamp', time.time() * 1000))
                latency_ms = our_fill_ts - target_fill_ts
                latency_str = f" | latency={latency_ms}ms"
            
            print(f"✅ Our fill: {side} {abs(delta):.4f} {symbol} @ ${price:.{price_decimals}f}{latency_str}")

        except Exception as e:
            print(f"⚠️  Error applying our fill: {e}")

    # ------------------------
    # Emergency flatten
    # ------------------------
    def emergency_flatten_all_positions(self):
        """Emergency flatten all positions"""
        if self.dry_run or not self.signer_client:
            print("⚠️  SAFETY flatten skipped (dry-run or missing signer).")
            return

        try:
            self._sync_positions_from_exchange(verbose=False, update_estimated=False)
            with self.state_lock:
                positions = dict(self.open_positions)

            if not positions:
                print("✅ SAFETY: No positions to flatten.")
                return

            print(f"🚨 SAFETY: Flattening {len(positions)} position(s)...")
            for market_index, pos in positions.items():
                if abs(pos) < 1e-8:
                    continue
                
                is_buy = pos < 0
                size = abs(pos)
                
                price = self._get_market_price(market_index, is_buy)
                if not price:
                    price = 1.0

                try:
                    self._place_order_internal(market_index, is_buy, size, price, is_closing=True)
                except Exception as e:
                    symbol = self._get_market_symbol(market_index)
                    print(f"❌ SAFETY: Failed to flatten {symbol}: {e}")

            print("✅ SAFETY: Flatten attempt complete.\n")

        except Exception as e:
            print(f"❌ SAFETY flatten error: {e}")

    # ------------------------
    # Signal handler
    # ------------------------
    def _signal_handler(self, sig, frame):
        print("\n\n🛑 Shutting down gracefully...")
        self.stop_event.set()
        
        # Flush remaining coalesced fills
        try:
            self._coalesce_flush_all()
        except:
            pass
        
        # Wait for queue to empty
        try:
            self.fill_queue.put(None)
            if self.dispatcher_thread:
                self.dispatcher_thread.join(timeout=2)
        except:
            pass
        
        # Shutdown executor
        if self.exec_pool:
            self.exec_pool.shutdown(wait=True, cancel_futures=False)
        
        # Close API client sessions
        if self.api_client:
            try:
                asyncio.run(self.api_client.close())
            except Exception as e:
                pass  # Ignore errors during cleanup
        
        print("✅ Shutdown complete")
        sys.exit(0)

    # ------------------------
    # WS stream
    # ------------------------
    async def stream_ws(self):
        """Stream WebSocket from Lighter"""
        while not self.stop_event.is_set():
            try:
                print(f"🔌 Connecting to Lighter WebSocket stream...")
                
                async with websockets.connect(
                    self.ws_url,
                    ping_interval=None,
                    ping_timeout=None,
                    max_size=10 * 1024 * 1024,
                    close_timeout=5
                ) as ws:
                    # Subscribe to target account fills
                    await ws.send(json.dumps({
                        "type": "subscribe",
                        "channel": f"account_all/{self.target_account_index}"
                    }))
                    
                    # Subscribe to our account fills if not dry run
                    if not self.dry_run and self.our_account_index:
                        await ws.send(json.dumps({
                            "type": "subscribe",
                            "channel": f"account_all/{self.our_account_index}"
                        }))
                    
                    print("✅ WebSocket stream started. Waiting for events...")
                    self.disconnect_start_time = None

                    while not self.stop_event.is_set():
                        try:
                            raw = await asyncio.wait_for(ws.recv(), timeout=30)
                            # Record receipt time immediately
                            recv_ms = int(time.time() * 1000)
                        except asyncio.TimeoutError:
                            # Periodic flush on timeout
                            try:
                                self._coalesce_flush_due(int(time.time() * 1000))
                            except:
                                pass
                            
                            # Send ping to keep connection alive
                            try:
                                await ws.send(json.dumps({"type": "ping"}))
                            except:
                                pass
                            continue

                        if not raw:
                            continue

                        try:
                            msg = json.loads(raw)
                        except:
                            continue

                        # Handle pong
                        if isinstance(msg, dict) and msg.get("type") == "ping":
                            await ws.send(json.dumps({"type": "pong"}))
                            continue

                        # Handle account_all updates
                        if isinstance(msg, dict) and msg.get("type") == "update/account_all":
                            account = msg.get("account")
                            trades_by_market = msg.get("trades", {})
                            
                            if not isinstance(trades_by_market, dict):
                                continue

                            # Process trades
                            for market_index, trades in trades_by_market.items():
                                if not isinstance(trades, list):
                                    continue
                                
                                for trade in trades:
                                    if not isinstance(trade, dict):
                                        continue

                                    # Use the recv_ms from when we received the WebSocket message
                                    trade["_recv_ms"] = recv_ms
                                    
                                    # Get event timestamp (Lighter uses seconds, convert to ms)
                                    event_timestamp = trade.get('timestamp', 0)
                                    if event_timestamp and event_timestamp > 0:
                                        # If timestamp looks like seconds (< 10^12), convert to ms
                                        if event_timestamp < 10**12:
                                            trade['timestamp'] = event_timestamp * 1000
                                    
                                    # Check if this is target's trade
                                    ask_id = trade.get('ask_account_id')
                                    bid_id = trade.get('bid_account_id')
                                    
                                    if account == self.target_account_index:
                                        # Target trader fill
                                        if ask_id == self.target_account_index:
                                            trade['side'] = 'SELL'
                                        elif bid_id == self.target_account_index:
                                            trade['side'] = 'BUY'
                                        else:
                                            continue
                                        
                                        # Add to coalescing buffer
                                        self._coalesce_add_fill(trade)
                                    
                                    elif not self.dry_run and account == self.our_account_index:
                                        # Our fill
                                        self._apply_our_fill_to_positions(trade)

            except Exception as e:
                print(f"❌ WebSocket error: {e}")

                # Flush coalesced fills on disconnect
                try:
                    self._coalesce_flush_all()
                except:
                    pass

                if self.disconnect_start_time is None:
                    self.disconnect_start_time = time.time()

                # Safety flatten if disconnected too long
                if self.safety_flatten_after_sec is not None:
                    elapsed = time.time() - self.disconnect_start_time
                    if elapsed >= self.safety_flatten_after_sec:
                        print(f"\n🚨 SAFETY: Disconnected for {elapsed:.1f}s (>= {self.safety_flatten_after_sec}s). Flattening positions...\n")
                        self.emergency_flatten_all_positions()
                        self.disconnect_start_time = time.time()

                print(f"🔁 Connection lost. Reconnecting in {self.reconnect_delay_sec} seconds...\n")
                await asyncio.sleep(self.reconnect_delay_sec)
                continue

    async def _run_async(self):
        """Async main loop"""
        # Save reference to main event loop
        self.main_loop = asyncio.get_running_loop()
        
        # Initialize SDK if in live mode
        if not self.dry_run:
            await self._initialize_lighter_sdk()
            
            # Fetch metadata
            try:
                await self._fetch_market_metadata_async()
            except Exception as e:
                print(f"⚠️  Could not fetch market metadata: {e}")
            
            # Sync positions
            try:
                await self._sync_positions_from_exchange_async(verbose=True)
            except Exception as e:
                print(f"⚠️  Could not sync positions: {e}")
        
        # Start pipeline
        self._start_async_pipeline()
        
        # Run WebSocket stream
        await self.stream_ws()

    def run(self):
        """Run the bot"""
        try:
            asyncio.run(self._run_async())
        except KeyboardInterrupt:
            print("\n🛑 Shutting down...")
            self.stop_event.set()


def main():
    if not os.path.exists('.env'):
        print("\n❌ No .env file found")
        print("📝 Setup: create .env file in this folder")
        print("   Then edit .env and set TARGET_ACCOUNT_INDEX\n")
        sys.exit(1)

    bot = CopyTradingBot()
    bot.run()


if __name__ == '__main__':
    main()
