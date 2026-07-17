#!/usr/bin/env python3
"""
Lighter Copy Trading Bot V1.9.8 - Educational Example

⚠️  WARNING: This bot trades with REAL money on MAINNET
    - Always test in DRY_RUN mode first
    - Never share your private keys
    - You can lose money - use at your own risk
    - Not financial advice

Multi-bot on one account: run this SAME file for every trader you copy.
Give each instance its own .env with a unique BOT_TAG (band #1 = 1000000,
band #2 = 2000000, ...), a unique API_KEY_INDEX, and MULTI_BOT_MODE=true.
The shared OUR_ACCOUNT_INDEX is fine; tags keep each bot's positions separate.

V1.9.8 Features:
- BOT_TAG is now read from .env (single code file serves all bot instances).
- MULTI_BOT_MODE flag: orphan detection uses THIS bot's own estimated position,
  so bots on a shared account never close each other's positions.
- Startup log shows multi-bot mode, BOT_TAG, and tag band; warns if BOT_TAG
  is left at default while multi-bot mode is on.

V1.9.7 Features:
- Position tagging via client_order_index to support multiple bots on same account
- Only closes orphan positions opened by THIS bot

V1.9.7 Fixes (multi-bot isolation):
- FIX: read the bot tag from the correct Lighter trade fields (ask_client_id /
  bid_client_id). The previous code read a non-existent 'client_order_index'
  field, so tags were never recovered from fills and the orphan filter never
  worked. (See Lighter WS Trade JSON.)
- FIX: tag-band width is now a fixed shared constant (TAG_WIDTH) instead of being
  tied to the BOT_TAG value, so adding bots no longer creates overlapping ranges.
- FIX: orphan closes are now tagged with this bot's BOT_TAG (was client_order_index=0).
- FIX: orphan close size is now bounded by THIS bot's estimated position, not the
  account-net position read from the API, so one bot no longer closes another
  bot's size on a shared market.
- NOTE: emergency_flatten remains intentionally global (account-wide) - it is an
  emergency measure and will flatten ALL positions across ALL bots by design.
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
        print("\n🤖 Lighter Trading Bot v1.9.9-17/07/2026")

        load_dotenv()

        # === Configuration ===
        self.base_url = os.getenv('LIGHTER_BASE_URL', 'https://mainnet.zklighter.elliot.ai')
        self.ws_url = os.getenv('LIGHTER_WS_URL', 'wss://mainnet.zklighter.elliot.ai/stream')
        
        self.target_account_index = int(os.getenv('TARGET_ACCOUNT_INDEX', '0'))
        self.copy_percentage = float(os.getenv('COPY_PERCENTAGE', '5.0'))
        # Per-coin copy percentage overrides: "HYPE:10.0,BTC:2.0"
        self.copy_percentage_overrides = {}
        overrides_raw = os.getenv('COPY_PERCENTAGE_OVERRIDES', '').strip()
        if overrides_raw:
            for pair in overrides_raw.split(','):
                parts = pair.strip().split(':')
                if len(parts) == 2:
                    coin = parts[0].strip().upper()
                    try:
                        self.copy_percentage_overrides[coin] = float(parts[1].strip())
                    except ValueError:
                        print(f"⚠️  Invalid COPY_PERCENTAGE_OVERRIDES value for {coin}, ignored")
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
        self.open_positions_est = {}      # {market_index: net size} optimistic/estimated (bumped at order placement)
        # V1.9.8 fix: this bot's own CONFIRMED position, updated ONLY by confirmed fills
        # (never by the optimistic bump at order placement). In multi-bot mode this is
        # the correct "before" baseline for the fill flush — open_positions_est cannot be
        # used for that because it was already bumped optimistically for the very order
        # whose fill we're processing, which would double-count the same delta.
        self.open_positions_confirmed = {}
        self.market_metadata = {}         # Cached metadata per market
        self.target_positions = {}        # {market_index: net size} - target trader reconstructed

        # ---- Pending closes + sync-on-miss rate limit ----
        self.pending_closes = {}          # {market_index: [ {frac, price, dir, ts_ms}, ... ]}
        self.last_sync_ts = {}            # {market_index: last_sync_time_sec}
        self.sync_on_miss_cooldown_sec = float(os.getenv("SYNC_ON_MISS_COOLDOWN_SEC", "0.5"))
        
        # ---- Order latency tracking ----
        self.order_target_timestamps = {}  # {market_index: target_fill_timestamp_ms} - for latency calculation
        
        # ---- Last observed prices (for market orders) ----
        self.last_observed_prices = {}  # {market_index: last_price} - from fills
        
        # ---- Fill coalescing (aggregate multiple fills into one log) ----
        self.pending_fills = {}  # {market_index: {'total_size': 0, 'total_cost': 0, 'fills': [], 'side': '', 'timer': None}}
        self.fill_coalesce_window_sec = 0.5  # Wait 500ms for more fills before logging
        
        # ---- PnL tracking per trade ----
        self.trade_entry_prices = {}  # {market_index: weighted_avg_entry_price}
        self.trade_entry_costs = {}   # {market_index: total_cost}
        
        # ---- Target PnL tracking (for comparison) ----
        # V1.9.8 REWRITE: target_entry_costs is now correctly REDUCED on each target
        # close (mirroring self.trade_entry_costs), so it always reflects the cost
        # basis of the target's CURRENTLY open portion, not a lifetime cumulative sum.
        # target_exit_costs is gone: instead, each target close computes its own exact
        # dollar PnL on the spot (per raw WS trade, no batching ambiguity) and that
        # value is queued in pending_target_close_pnl for the matching copy-order fill
        # to consume — a direct dollar comparison instead of a derived cost ratio.
        self.target_entry_prices = {}  # {market_index: weighted_avg_entry_price}
        self.target_entry_costs = {}   # {market_index: cost basis of currently-open portion}
        self.target_position_sizes = {}  # {market_index: total_size}
        self.pending_target_close_pnl = {}  # {market_index: accumulated $ PnL target realized, awaiting our matching fill}
        # V1.9.8: last time we processed a live WS trade for this market, used to gate
        # the periodic API reconciliation so it never races an in-flight WS fill for the
        # same trade (which would double-count the position — see _sync_target_actual_positions_async).
        self.last_target_ws_update_ts = {}
        
        # ---- Order price tracking (for slippage calculation) ----
        self.order_intended_prices = {}  # {market_index: intended_price} - price we sent in order
        
        # ---- Order placement lock (prevent nonce conflicts) ----
        self.order_lock = threading.Lock()
        
        # ===== V1.9.4 / V1.9.7: Position Tagging =====
        # Each bot tags its orders with a unique client_order_index to identify ownership.
        # Tags live in disjoint, fixed-width bands so multiple bots on the same account
        # never collide. Band for a bot = [BOT_TAG, BOT_TAG + TAG_WIDTH).
        #   Bot 1: BOT_TAG = 1 * TAG_WIDTH
        #   Bot 2: BOT_TAG = 2 * TAG_WIDTH
        #   Bot N: BOT_TAG = N * TAG_WIDTH
        # client_order_index is a uint48 (max 2^48-1 ~ 2.8e14), so there is plenty of room.
        self.TAG_WIDTH = 1_000_000              # V1.9.7: fixed band width, shared by all bots
        # V1.9.8: BOT_TAG is read from env so a single code file serves all bot instances.
        # Each bot must set a unique BOT_TAG in its .env (band #1 = 1000000, #2 = 2000000, ...).
        # Falls back to band #1 if unset (single-bot default).
        self.BOT_TAG = int(os.getenv('BOT_TAG', str(1 * self.TAG_WIDTH)))
        self.order_counter = 0
        self.order_counter_lock = threading.Lock()
        # Track which bot opened each position: {market_index: client_order_index}
        self.position_tags = {}
        
        # ===== V1.9.8: Multi-bot mode =====
        # When multiple bots share the SAME Lighter account, the exchange reports a
        # NET position that mixes all bots. In that case open_positions (from API) can't
        # tell which bot owns what, so orphan detection must rely ONLY on this bot's own
        # estimated position (open_positions_est), which is updated exclusively by this
        # bot's own fills. Set MULTI_BOT_MODE=true when running >1 bot on one account.
        self.multi_bot_mode = os.getenv('MULTI_BOT_MODE', 'false').lower() in ('true', '1', 'yes')
        # Track whether BOT_TAG was explicitly set (for a safety warning in multi-bot mode)
        self._bot_tag_was_explicit = os.getenv('BOT_TAG') is not None


        # ---- Periodic target state reconciliation ----
        self.target_state_sync_interval_sec = float(os.getenv("TARGET_STATE_SYNC_INTERVAL_SEC", "3.0"))
        self.orphan_close_cooldown_sec = float(os.getenv("ORPHAN_CLOSE_COOLDOWN_SEC", "2.0"))  # Increased from 1.0
        self.target_positions_actual = {}   # {market_index: net size} from API
        self.last_orphan_close_ts = {}      # {market_index: last_attempt_time_sec}
        # V1.9.8: count consecutive orphan-close attempts per market. If we keep trying
        # to close the same market without the estimate ever clearing, the estimate is a
        # ghost (real position already gone) — after a few tries we force-reconcile it.
        self.orphan_close_attempts = {}     # {market_index: consecutive attempt count}
        self.orphan_close_attempts_max = int(os.getenv("ORPHAN_CLOSE_ATTEMPTS_MAX", "3"))
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
        if self.copy_percentage_overrides:
            overrides_str = ", ".join(f"{coin}: {pct}%" for coin, pct in self.copy_percentage_overrides.items())
            print(f"📊 Copy overrides:  {overrides_str}")
        print(f"🧪 Dry run mode: {self.dry_run}")
        if self.multi_bot_mode:
            print(f"🤖 Multi-bot mode: ON (BOT_TAG={self.BOT_TAG}, band=[{self.BOT_TAG}, {self.BOT_TAG + self.TAG_WIDTH}))")
            if not self._bot_tag_was_explicit:
                print(f"   ⚠️  WARNING: BOT_TAG not set in .env — using default {self.BOT_TAG}.")
                print(f"   ⚠️  Each bot on the same account MUST have a unique BOT_TAG!")
        else:
            print(f"🤖 Multi-bot mode: OFF (single bot on this account, BOT_TAG={self.BOT_TAG})")
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
                print(f"❌ Error in reconcile loop: {e}")
                import traceback
                traceback.print_exc()

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

    def _round_size_floor(self, market_index, size):
        """
        Floor size to market precision (V1.9.7).

        Used for CLOSES, where rounding to nearest could round UP above the actual
        position and get the residual rejected by reduce_only. Flooring guarantees
        we never request more than we hold.
        """
        decimals = 4
        if market_index in self.market_metadata:
            decimals = self.market_metadata[market_index].get('size_decimals', 4)
        factor = 10 ** decimals
        return math.floor(abs(size) * factor) / factor

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
            response = await self.account_api.account(by="index", value=str(self.our_account_index))
            
            new_positions = {}
            
            # Try new format (like target sync) with 'accounts' list
            if response and hasattr(response, 'accounts') and len(response.accounts) > 0:
                account = response.accounts[0]
                
                if hasattr(account, 'positions'):
                    for pos in account.positions:
                        market_index = pos.market_id
                        position_size = float(pos.position or 0)
                        sign = getattr(pos, 'sign', 1)
                        net_size = position_size * sign
                        
                        if abs(net_size) > 1e-8:
                            new_positions[market_index] = net_size
            
            # Try old format (direct positions)
            elif response and hasattr(response, 'positions'):
                for pos in response.positions:
                    market_index = pos.market_id
                    position_size = float(pos.position or 0)
                    sign = getattr(pos, 'sign', 1)
                    net_size = position_size * sign
                    
                    if abs(net_size) > 1e-8:
                        new_positions[market_index] = net_size

            with self.state_lock:
                self.open_positions = new_positions
                # V1.9.8: In multi-bot mode, NEVER overwrite our own estimated position
                # with the shared account net — it would blend in other bots' positions.
                # open_positions_est is our bot's own position, tracked via our own fills.
                if update_estimated and not self.multi_bot_mode:
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
            if verbose:
                print(f"⚠️  Error syncing positions: {e}")
                import traceback
                traceback.print_exc()

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

                # V1.9.8: Reconcile the WS-reconstructed target position with reality.
                # OPEN/CLOSE classification relies on self.target_positions, which is
                # built incrementally from live WS fills. If the WS misses target trades
                # (frequent on reconnects), that reconstruction drifts and a real OPEN can
                # be misread as a CLOSE (or vice-versa), so the bot fails to copy it.
                # The API snapshot is ground truth, so we realign to it here.
                #
                # RACE CONDITION GUARD: a REST snapshot can reflect a trade that already
                # executed exchange-side moments before the corresponding WS event has
                # been delivered to us. If we reconciled blindly, that trade would be
                # double-counted: once by this reconciliation, once again when the
                # (delayed) WS event lands and adds its own delta on top. To prevent
                # this, we only reconcile a market if there has been NO WS-driven update
                # for it in the last RECONCILE_QUIET_PERIOD_SEC — i.e. only during a
                # genuine quiet period (disconnect, missed trade), never while the WS
                # feed is actively delivering trades for that market.
                RECONCILE_QUIET_PERIOD_SEC = 2.0
                now_ts = time.time()

                for market_index, real_net in new_target_positions.items():
                    last_ws = self.last_target_ws_update_ts.get(market_index, 0.0)
                    if (now_ts - last_ws) < RECONCILE_QUIET_PERIOD_SEC:
                        continue  # WS is live for this market — don't race it
                    recon = self.target_positions.get(market_index, 0.0)
                    real_sign = 0 if abs(real_net) < 1e-8 else math.copysign(1, real_net)
                    recon_sign = 0 if abs(recon) < 1e-8 else math.copysign(1, recon)
                    gap = abs(real_net - recon)
                    tol = max(abs(real_net) * 0.05, 1e-6)  # 5% or dust tolerance
                    if real_sign != recon_sign or gap > tol:
                        self.target_positions[market_index] = real_net
                        self.target_position_sizes[market_index] = abs(real_net)
                        print(f"   🔄 Target position resynced from API: "
                              f"{self._get_market_symbol(market_index)} "
                              f"{recon:.4f} → {real_net:.4f}")

                # Markets the target has fully exited (absent from the API snapshot)
                # but still shown as open in our reconstruction: reset them to flat.
                # Same quiet-period guard applies.
                for market_index in list(self.target_positions.keys()):
                    if market_index in new_target_positions:
                        continue
                    if abs(self.target_positions.get(market_index, 0.0)) <= 1e-8:
                        continue
                    last_ws = self.last_target_ws_update_ts.get(market_index, 0.0)
                    if (now_ts - last_ws) < RECONCILE_QUIET_PERIOD_SEC:
                        continue
                    old = self.target_positions[market_index]
                    self.target_positions[market_index] = 0.0
                    self.target_position_sizes.pop(market_index, None)
                    self.target_entry_costs.pop(market_index, None)
                    self.target_entry_prices.pop(market_index, None)
                    print(f"   🔄 Target flat per API: "
                          f"{self._get_market_symbol(market_index)} "
                          f"{old:.4f} → 0 (WS had missed the close)")

        except Exception as e:
            if not self.stop_event.is_set():
                e_str = str(e)
                code = next((c for c in ['500', '502', '503', '504', '429'] if c in e_str), None)
                if code:
                    print(f"⚠️  API sync unavailable (HTTP {code}), retrying...")
                else:
                    print(f"⚠️  Error syncing target positions: {type(e).__name__}: {e_str[:100]}")

    def _sync_target_actual_positions(self):
        """Sync target trader's actual positions (wrapper for thread)"""
        if self.stop_event.is_set():
            return
        
        if not self.account_api:
            return
            
        if not self.main_loop:
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
                e_str = str(e)
                code = next((c for c in ['500', '502', '503', '504', '429'] if c in e_str), None)
                if code:
                    print(f"⚠️  API sync unavailable (HTTP {code}), retrying...")
                else:
                    print(f"⚠️  Target position sync error: {type(e).__name__}: {e_str[:100]}")

    def _check_orphan_positions(self):
        """
        V1.9.4: Check orphan positions but ONLY close positions opened by THIS bot.
        
        Uses position_tags to identify ownership via client_order_index:
        - Bot 1 (Lighter→Lighter):     BOT_TAG = 1_000_000
        - Bot 2 (Hyperliquid→Lighter): BOT_TAG = 2_000_000
        
        If target is flat but we have a position with OUR tag, close it using
        the exact same logic as normal closes (reduce_only=True).
        """
        if self.stop_event.is_set() or self.dry_run:
            return
        
        if not self.signer_client or not self.account_api:
            return

        # CRITICAL: Sync OUR positions first (to detect manual positions)
        # Wait a bit longer to let pending fills arrive
        try:
            if self.main_loop and self.main_loop.is_running():
                # Sleep 100ms to let pending fills process
                time.sleep(0.1)
                
                future = asyncio.run_coroutine_threadsafe(
                    self._sync_positions_from_exchange_async(verbose=False),
                    self.main_loop
                )
                future.result(timeout=2)
        except Exception as e:
            # Silent - will retry in 2 seconds
            pass

        # Get positions
        with self.state_lock:
            target_actual = dict(self.target_positions_actual)
            # V1.9.8: In multi-bot mode, use THIS bot's own estimated position
            # (open_positions_est), not the shared account net (open_positions).
            # The account net blends all bots and would trigger false orphans.
            if self.multi_bot_mode:
                our_positions = dict(self.open_positions_est)
            else:
                our_positions = dict(self.open_positions)
            position_tags = dict(self.position_tags)  # V1.9.4: Get tags

        if not our_positions:
            return

        now = time.time()

        # Check each position
        for market_index, our_size in our_positions.items():
            if abs(our_size) < 1e-8:
                continue
            
            # V1.9.4/V1.9.7: Check if this position belongs to THIS bot.
            # Ownership = tag falls inside this bot's fixed-width band.
            tag = position_tags.get(market_index, 0)
            
            # Multi-bot: If tag is 0, this position came from sync without known origin
            # (likely opened by another bot, or manual trade)
            # Ignore it to avoid closing other bots' positions
            if tag == 0:
                continue
            
            if tag < self.BOT_TAG or tag >= self.BOT_TAG + self.TAG_WIDTH:
                # This position was NOT opened by this bot - skip it
                # (could be from bot 2, or manual trade, or bot with different tag)
                continue
            
            target_size = target_actual.get(market_index, 0.0)
            
            symbol = self._get_market_symbol(market_index)
            
            # Skip if target also has position
            if abs(target_size) >= 1e-8:
                continue
            
            # ORPHAN: Target = 0, We ≠ 0, and it's OUR position
            print(f"\n🚨 ORPHAN DETECTED: {symbol} (we: {our_size:.4f}, target: 0, tag: {tag})")
            
            # Rate-limit
            with self.state_lock:
                last = float(self.last_orphan_close_ts.get(market_index, 0.0))
            
            if now - last < self.orphan_close_cooldown_sec:
                remaining = self.orphan_close_cooldown_sec - (now - last)
                print(f"   ⏳ Rate limited, retry in {remaining:.1f}s")
                continue
            
            with self.state_lock:
                self.last_orphan_close_ts[market_index] = now
                # V1.9.8: track consecutive attempts on this market
                attempts = self.orphan_close_attempts.get(market_index, 0) + 1
                self.orphan_close_attempts[market_index] = attempts

            # V1.9.8: If we've tried repeatedly without the estimate clearing, the
            # estimate is almost certainly a ghost (real position already gone). Force a
            # fresh sync and reconcile our estimate to reality instead of looping.
            if attempts > self.orphan_close_attempts_max:
                try:
                    if self.main_loop and self.main_loop.is_running():
                        fut = asyncio.run_coroutine_threadsafe(
                            self._sync_positions_from_exchange_async(verbose=False),
                            self.main_loop
                        )
                        fut.result(timeout=2)
                except Exception:
                    pass
                with self.state_lock:
                    real_net = self.open_positions.get(market_index, 0.0)
                    # Reconcile our estimate to the real account net (bounded to our side).
                    if abs(real_net) < 1e-8:
                        self.open_positions_est.pop(market_index, None)
                        self.position_tags.pop(market_index, None)
                    else:
                        self.open_positions_est[market_index] = real_net
                    self.orphan_close_attempts.pop(market_index, None)
                print(f"   ♻️  {symbol}: {attempts-1} close attempts with no effect — "
                      f"estimate reconciled to real net {real_net:.4f}, stopping loop")
                continue

            # V1.9.7: Derive the close hint from THIS bot's estimated position when
            # available (it carries this bot's own sign/size), falling back to the
            # account-net only if we have no estimate. _close_orphan_position re-derives
            # and bounds these values authoritatively.
            with self.state_lock:
                our_est_size = self.open_positions_est.get(market_index, our_size)
            ref_size = our_est_size if abs(our_est_size) > 1e-8 else our_size
            is_buy = ref_size < 0
            size = abs(ref_size)
            
            try:
                # Just close it with market order
                self._close_orphan_position(market_index, size, 0, is_buy)
            except Exception as e:
                print(f"❌ RECONCILE: Failed to close {symbol}: {e}")
                import traceback
                traceback.print_exc()
    
    def _get_market_price_for_orphan(self, market_index, is_buy):
        """
        Get market price specifically for orphan closes.
        
        STRATEGY:
        1. Try custom logic with fallbacks
        2. If that fails, use existing _get_market_price() as ultimate fallback
        
        Returns None if price unavailable.
        """
        if not self.order_api:
            print(f"   🔍 DEBUG: order_api is None")
            return None
        
        if not self.main_loop:
            print(f"   🔍 DEBUG: main_loop is None")
            return None
        
        if not self.main_loop.is_running():
            print(f"   🔍 DEBUG: main_loop is not running")
            return None
        
        try:
            future = asyncio.run_coroutine_threadsafe(
                self._get_market_price_for_orphan_async(market_index, is_buy),
                self.main_loop
            )
            result = future.result(timeout=5)
            if result:
                print(f"   🔍 DEBUG: Got price {result} for market {market_index}")
                return result
            else:
                print(f"   🔍 DEBUG: Price fetch returned None, trying fallback...")
                # FALLBACK: Try the existing _get_market_price() function
                fallback_price = self._get_market_price(market_index, is_buy)
                if fallback_price:
                    print(f"   🔍 DEBUG: Fallback succeeded with price {fallback_price}")
                    return fallback_price
                else:
                    print(f"   🔍 DEBUG: Fallback also failed")
                    return None
        except asyncio.TimeoutError:
            print(f"   🔍 DEBUG: Timeout fetching price for market {market_index}")
            # Try fallback
            print(f"   🔍 DEBUG: Trying fallback after timeout...")
            return self._get_market_price(market_index, is_buy)
        except Exception as e:
            print(f"   🔍 DEBUG: Error fetching price for market {market_index}: {type(e).__name__}: {e}")
            import traceback
            traceback.print_exc()
            # Try fallback
            print(f"   🔍 DEBUG: Trying fallback after exception...")
            return self._get_market_price(market_index, is_buy)

    async def _get_market_price_for_orphan_async(self, market_index, is_buy):
        """
        Async version with fallback logic:
        1. Try to get best ask (for BUY) or best bid (for SELL)
        2. If missing, calculate mid-price
        3. If both missing, return None
        """
        try:
            print(f"   🔍 DEBUG: Fetching orderbook for market {market_index}")
            order_book_response = await self.order_api.order_book_details(market_id=str(market_index))
            
            if not order_book_response:
                print(f"   🔍 DEBUG: order_book_response is None")
                return None
            
            # Extract order book
            if hasattr(order_book_response, 'order_book_details'):
                order_book = order_book_response.order_book_details
            elif hasattr(order_book_response, 'spot_order_book_details'):
                order_book = order_book_response.spot_order_book_details
            else:
                print(f"   🔍 DEBUG: No order_book_details or spot_order_book_details attribute")
                print(f"   🔍 DEBUG: Response attributes: {dir(order_book_response)}")
                return None
            
            if not order_book:
                print(f"   🔍 DEBUG: order_book is None")
                return None
            
            # Extract prices
            best_bid = None
            best_ask = None
            
            if hasattr(order_book, 'bids') and order_book.bids:
                best_bid = float(order_book.bids[0].price)
                print(f"   🔍 DEBUG: best_bid = {best_bid}")
            else:
                print(f"   🔍 DEBUG: No bids available")
            
            if hasattr(order_book, 'asks') and order_book.asks:
                best_ask = float(order_book.asks[0].price)
                print(f"   🔍 DEBUG: best_ask = {best_ask}")
            else:
                print(f"   🔍 DEBUG: No asks available")
            
            # Priority logic for orphan closes
            if is_buy:
                if best_ask and best_ask > 0:
                    print(f"   🔍 DEBUG: Using best_ask {best_ask} for BUY")
                    return best_ask
                elif best_bid and best_bid > 0:
                    print(f"   🔍 DEBUG: Fallback to best_bid {best_bid} for BUY")
                    return best_bid
            else:
                if best_bid and best_bid > 0:
                    print(f"   🔍 DEBUG: Using best_bid {best_bid} for SELL")
                    return best_bid
                elif best_ask and best_ask > 0:
                    print(f"   🔍 DEBUG: Fallback to best_ask {best_ask} for SELL")
                    return best_ask
            
            # Last resort: mid-price
            if best_bid and best_ask and best_bid > 0 and best_ask > 0:
                mid = (best_bid + best_ask) / 2.0
                print(f"   🔍 DEBUG: Using mid-price {mid}")
                return mid
            
            print(f"   🔍 DEBUG: No valid price found")
            return None
                
        except Exception as e:
            print(f"   🔍 DEBUG: Exception in _get_market_price_for_orphan_async: {type(e).__name__}: {e}")
            import traceback
            traceback.print_exc()
            return None

    def _close_orphan_position(self, market_index, size, price, is_buy):
        """
        Close orphan position using MARKET ORDER via SDK
        
        Uses client.create_market_order() - much simpler!
        """
        symbol = self._get_market_symbol(market_index)
        
        # CRITICAL: Sync our actual position from exchange FIRST (like Hyperliquid)
        # This prevents closing a position that was already closed by normal flow
        try:
            if self.main_loop and self.main_loop.is_running():
                future = asyncio.run_coroutine_threadsafe(
                    self._sync_positions_from_exchange_async(verbose=False),
                    self.main_loop
                )
                future.result(timeout=2)
        except Exception:
            pass  # Continue anyway, use cached position
        
        # Double-check we still have the position AFTER sync.
        # V1.9.7 multi-bot isolation: bound the close to THIS bot's own estimated
        # position, not the account-net position returned by the API. On a market
        # where several bots hold positions, open_positions (API net) aggregates all
        # of them; closing abs(net) would close the other bots' size too. The orphan
        # caller already verified ownership via the tag band, so open_positions_est
        # (which this bot maintains from its own tagged fills) is the right ceiling.
        with self.state_lock:
            account_net = self.open_positions.get(market_index, 0.0)
            our_est = self.open_positions_est.get(market_index, account_net)

        # V1.9.8: Ghost-estimate reconciliation.
        # We just synced account_net from the exchange (above). In multi-bot mode we
        # deliberately never overwrite open_positions_est from the API, so if our
        # estimate drifted (missed fill, restart, prior close that fully filled), it can
        # claim a position the account no longer holds. A reduce_only close would then
        # fill nothing, no fill event would arrive, the estimate would never update, and
        # the orphan check would loop forever. Detect that here: if the real account has
        # no position on our side, our estimate is a ghost — clear it and stop.
        est_sign = 0 if abs(our_est) < 1e-8 else math.copysign(1, our_est)
        net_sign = 0 if abs(account_net) < 1e-8 else math.copysign(1, account_net)
        if est_sign != 0 and net_sign != est_sign:
            # Either the account is flat, or it only holds the OTHER sign (another bot).
            # Our estimated position on this market cannot really exist. Reconcile.
            with self.state_lock:
                self.open_positions_est.pop(market_index, None)
                self.position_tags.pop(market_index, None)
            print(f"   ♻️  Estimate reconciled: no real {symbol} position on our side "
                  f"(est was {our_est:.4f}, account net {account_net:.4f}) — cleared, skipping close")
            return

        # Use our own estimated position as the source of truth for sign and size.
        current_pos = our_est if abs(our_est) > 1e-8 else 0.0

        if abs(current_pos) < 1e-8:
            return  # Already closed (per our own tracking), skip silently

        # Never try to close more than the account actually holds, in case our
        # estimate drifted above the real net (e.g. partial fills, restarts).
        if abs(account_net) > 1e-8:
            current_pos = math.copysign(min(abs(current_pos), abs(account_net)), current_pos)

        # 2. Authoritatively derive size AND direction from current_pos (this bot's
        #    bounded estimate). To reduce a LONG we SELL; to reduce a SHORT we BUY.
        is_buy = current_pos < 0
        size = min(size, abs(current_pos)) if size and size > 0 else abs(current_pos)

        # 3. Round the size DOWN to market precision so we never exceed the position
        #    (reduce_only would reject the excess; flooring avoids the round-up case).
        size = self._round_size_floor(market_index, size)

        # V1.9.8: Un-closeable residual detection.
        # Lighter enforces a per-market minimum lot (min_size / min_base_amount) and a
        # minimum notional. A residual below these CANNOT be closed on its own: the order
        # is accepted by create_order but never matches, so it silently does nothing and
        # the orphan loop repeats forever printing a misleading "Closed successfully".
        # Detect that here and stop trying — the dust stays until the position is next
        # increased (a larger order can carry it) or closed by the account-wide flatten.
        market_meta = self.market_metadata.get(market_index, {})
        try:
            min_lot = float(market_meta.get('min_size', 0) or 0)
        except (TypeError, ValueError):
            min_lot = 0.0
        with self.state_lock:
            last_price = self.last_observed_prices.get(market_index, 0.0)
        residual_notional = abs(size) * last_price if last_price else 0.0
        below_min_lot = min_lot > 0 and abs(size) < min_lot
        below_min_notional = last_price > 0 and residual_notional < self.min_notional_usd
        if size > 0 and (below_min_lot or below_min_notional):
            reason = []
            if below_min_lot:
                reason.append(f"size {size:.6f} < min lot {min_lot:.6f}")
            if below_min_notional:
                reason.append(f"notional ${residual_notional:.2f} < min ${self.min_notional_usd:.2f}")
            with self.state_lock:
                # Align our estimate to the real residual so the number stops drifting,
                # but keep the tag so a future larger order can still carry/close it.
                self.open_positions_est[market_index] = account_net
                self.orphan_close_attempts.pop(market_index, None)
            print(f"   ⏹️  {symbol}: residual not closeable ({'; '.join(reason)}). "
                  f"Leaving {account_net:.6f} until next fill or global flatten.")
            return

        # V1.9.8: Dust reconciliation. If the real account only holds a residual that
        # rounds to zero at market precision (dust), there is nothing meaningful left to
        # close, yet our estimate may still claim a larger position. Closing would loop
        # forever on sub-minimum size. Reconcile our estimate to the real net and stop.
        real_side_size = abs(account_net) if net_sign == est_sign else 0.0
        if size <= 0 or self._round_size_floor(market_index, real_side_size) <= 0:
            with self.state_lock:
                if abs(account_net) < 1e-8 or net_sign != est_sign:
                    # Nothing of ours left on the account.
                    self.open_positions_est.pop(market_index, None)
                    self.position_tags.pop(market_index, None)
                    self.orphan_close_attempts.pop(market_index, None)
                    reconciled_to = 0.0
                else:
                    # Account still holds a (dust) position on our side: align estimate
                    # to reality so we stop claiming the drifted, larger size.
                    self.open_positions_est[market_index] = account_net
                    self.orphan_close_attempts.pop(market_index, None)
                    reconciled_to = account_net
            print(f"   ♻️  {symbol}: only dust left (est {our_est:.4f}, account net "
                  f"{account_net:.4f}) — estimate reconciled to {reconciled_to:.4f}, stopping")
            return

        print(f"   🧹 Closing orphan: {'BUY' if is_buy else 'SELL'} {size:.4f} {symbol}")
        
        try:
            # Use market order - much simpler!
            self._place_market_order_for_orphan(market_index, is_buy, size, symbol)
        except Exception as e:
            print(f"   ❌ Failed: {e}")
    
    def _place_market_order_for_orphan(self, market_index, is_buy, size, symbol):
        """
        Place aggressive LIMIT order to close orphan (same as normal close + reduce_only).
        
        Uses exact same create_order call as normal closes, but with:
        - Very aggressive price (10% margin) for immediate fill
        - reduce_only=True to prevent inverse position opening
        """
        
        if self.dry_run:
            print(f"🧪 DRY RUN: Would LIMIT {'BUY' if is_buy else 'SELL'} {size:.4f} {symbol}")
            return
        
        if not self.signer_client:
            print(f"❌ ERROR: SignerClient not initialized")
            return
        
        # Use run_coroutine_threadsafe
        try:
            if self.main_loop and self.main_loop.is_running():
                future = asyncio.run_coroutine_threadsafe(
                    self._place_market_order_for_orphan_async(market_index, is_buy, size, symbol),
                    self.main_loop
                )
                future.result(timeout=10)
            else:
                print(f"❌ ERROR: Main event loop not available")
        except Exception as e:
            print(f"❌ Market order failed: {e}")
            raise
    
    async def _place_market_order_for_orphan_async(self, market_index, is_buy, size, symbol):
        """
        Place MARKET order with reduce_only=True (from Lighter official docs).
        
        Uses create_order with:
        - ORDER_TYPE_MARKET
        - ORDER_TIME_IN_FORCE_IMMEDIATE_OR_CANCEL
        - reduce_only=True (prevents inverse position opening)
        - DEFAULT_IOC_EXPIRY
        """
        try:
            # Get market metadata
            market_meta = self.market_metadata.get(market_index, {})
            size_decimals = market_meta.get('size_decimals', 4)
            price_decimals = market_meta.get('price_decimals', 2)
            
            # Convert size to base_amount
            base_amount = round(size * (10 ** size_decimals))
            
            # Calculate worst acceptable price with 50% margin
            with self.state_lock:
                last_price = self.last_observed_prices.get(market_index)
            
            if last_price and last_price > 0:
                # Use 50% margin
                safety_margin = 0.50
                
                if is_buy:
                    worst_price = last_price * (1 + safety_margin)
                else:
                    worst_price = last_price * (1 - safety_margin)
                
                price_int = round(worst_price * (10 ** price_decimals))
            else:
                # Fallback estimates
                if 'BTC' in symbol.upper():
                    if is_buy:
                        price_int = round(150000 * (10 ** price_decimals))
                    else:
                        price_int = round(10000 * (10 ** price_decimals))
                elif 'ETH' in symbol.upper():
                    if is_buy:
                        price_int = round(10000 * (10 ** price_decimals))
                    else:
                        price_int = round(500 * (10 ** price_decimals))
                else:
                    if is_buy:
                        price_int = round(10000 * (10 ** price_decimals))
                    else:
                        price_int = round(0.01 * (10 ** price_decimals))
            
            # CRITICAL: Serialize with lock
            loop = asyncio.get_event_loop()

            # V1.9.7: Tag the orphan close with this bot's band so the resulting fill
            # is attributable to this bot (was client_order_index=0, which made close
            # fills indistinguishable between bots).
            with self.order_counter_lock:
                self.order_counter += 1
                orphan_cid = self.BOT_TAG + (self.order_counter % self.TAG_WIDTH)

            async def _create_order_with_lock():
                await loop.run_in_executor(None, self.order_lock.acquire)
                try:
                    # EXACT copy from Lighter docs - use full constant names!
                    result = await self.signer_client.create_order(
                        market_index=market_index,
                        client_order_index=orphan_cid,  # V1.9.7: tagged (was 0)
                        base_amount=base_amount,
                        price=price_int,
                        is_ask=not is_buy,
                        order_type=self.signer_client.ORDER_TYPE_MARKET,
                        time_in_force=self.signer_client.ORDER_TIME_IN_FORCE_IMMEDIATE_OR_CANCEL,
                        reduce_only=True,  # ✅ CRITICAL: Prevents inverse position!
                        order_expiry=self.signer_client.DEFAULT_IOC_EXPIRY,
                    )
                    return result
                finally:
                    self.order_lock.release()
            
            result = await _create_order_with_lock()
            
            # result is a tuple: (tx, tx_hash, error)
            tx, tx_hash, err = result
            
            if err:
                print(f"   ⚠️  Error: {err}")
            else:
                print(f"   ✅ Closed successfully")
        
        except Exception as e:
            print(f"   ❌ Exception: {e}")
            raise
    
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
                # V1.9.8: mark this market as "live" so the periodic API reconciliation
                # won't race this same trade (see _sync_target_actual_positions_async).
                self.last_target_ws_update_ts[market_index] = time.time()
                
                # Track target's PnL for comparison
                is_target_opening = (current_target == 0) or (current_target > 0 and delta > 0) or (current_target < 0 and delta < 0)
                is_target_closing = (current_target > 0 and delta < 0) or (current_target < 0 and delta > 0)
                
                # V1.9.8: dollar PnL the TARGET realized on this specific trade (close
                # only). Computed here, per raw WS trade — no coalescing/batching
                # ambiguity on this side, so this is always exact.
                target_trade_pnl = None
                
                if is_target_opening:
                    # Opening or adding - update entry price
                    old_cost = self.target_entry_costs.get(market_index, 0)
                    new_cost = old_cost + (size * price)
                    
                    self.target_entry_costs[market_index] = new_cost
                    self.target_position_sizes[market_index] = abs(new_target)
                    if abs(new_target) > 0:
                        self.target_entry_prices[market_index] = new_cost / abs(new_target)
                
                elif is_target_closing:
                    # V1.9.8 FIX: previously this only accumulated an ever-growing
                    # "target_exit_costs" total without ever reducing target_entry_costs,
                    # so any market opened/closed more than once in a session ended up
                    # with a meaningless, unbounded cost basis. Now: reduce entry cost
                    # proportionally (like our own side already does) and compute this
                    # trade's exact $ PnL directly from target's own entry/exit prices.
                    entry_cost = self.target_entry_costs.get(market_index, 0)
                    close_ratio = min(size / abs(current_target), 1.0) if abs(current_target) > 1e-8 else 0.0
                    closed_entry_cost = entry_cost * close_ratio
                    exit_value = size * price
                    if current_target > 0:  # target was LONG, this SELL closes it
                        target_trade_pnl = exit_value - closed_entry_cost
                    else:  # target was SHORT, this BUY closes it
                        target_trade_pnl = closed_entry_cost - exit_value
                    self.target_entry_costs[market_index] = entry_cost - closed_entry_cost
                    self.target_position_sizes[market_index] = abs(new_target)
                    
                    if abs(new_target) < 1e-8:
                        # Target is fully flat on this market: reset its cost tracking
                        # so a future re-open starts from a clean basis.
                        self.target_entry_costs.pop(market_index, None)
                        self.target_entry_prices.pop(market_index, None)
                        self.target_position_sizes.pop(market_index, None)
            
            # Now current_target has the OLD position (before this fill)
            # new_target has the NEW position (after this fill)
            
            # Determine if this is a closing trade EARLY
            # A trade is a close if it reduces the target's position
            is_closing = False
            if is_buy and current_target < 0:  # Buying to close short
                is_closing = True
            elif is_sell and current_target > 0:  # Selling to close long
                is_closing = True

            # Calculate our order size (use per-coin override si disponible)
            effective_copy_pct = self.copy_percentage_overrides.get(symbol, self.copy_percentage)
            our_size = size * (effective_copy_pct / 100.0)
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
                
                # V1.9.8: queue the target's exact $ PnL for this close so our matching
                # fill (processed later, async, in _flush_pending_fills) can show a
                # dollar-accurate comparison instead of a derived ratio. Only queued once
                # we've committed to actually placing a corresponding order — if we skip
                # copying this event (filtered, zero-size, etc.) we simply don't queue it,
                # since there will be no fill to consume it anyway.
                if target_trade_pnl is not None:
                    with self.state_lock:
                        self.pending_target_close_pnl[market_index] = (
                            self.pending_target_close_pnl.get(market_index, 0.0) + target_trade_pnl
                        )
                
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

        # Stocker prix du target AVANT ajustement (pour calcul slippage au fill)
        target_price = price

        # Adjust price for slippage (prix du limit order placé sur l'exchange)
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
            
            # Store target fill timestamp et prix TARGET (avant slippage) pour calcul slippage
            if target_fill_time_ms:
                self.order_target_timestamps[market_index] = target_fill_time_ms
                self.order_intended_prices[market_index] = target_price  # Prix du TARGET, pas notre ordre

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
            print(f"   📋 Order: {side_str} {size:.4f} {symbol} @ ${price:.4f}, is_closing={is_closing}")
            print(f"   🔍 Exception type: {type(e).__name__}")
            import traceback
            traceback.print_exc()
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
            
            # CRITICAL: Only check minimum size for OPENS, not CLOSES
            # Closes (reduce_only=True) can be below minimum
            if not is_closing and size < min_size:
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
            
            # V1.9.4/V1.9.7: Generate tagged client_order_index for position tracking
            with self.order_counter_lock:
                self.order_counter += 1
                # BOT_TAG + (counter mod TAG_WIDTH) keeps the index inside this bot's band.
                # Note: client_order_index must be unique across all markets (Lighter docs),
                # so the band must be wide enough for the order volume of a session.
                tagged_client_order_index = self.BOT_TAG + (self.order_counter % self.TAG_WIDTH)
            
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
                        time_in_force=self.signer_client.ORDER_TIME_IN_FORCE_IMMEDIATE_OR_CANCEL,  # IOC: fill now or cancel, never rests in book
                        reduce_only=is_closing,
                        order_expiry=self.signer_client.DEFAULT_IOC_EXPIRY,
                        client_order_index=tagged_client_order_index  # V1.9.4: Tagged with BOT_TAG
                    )
                    return result
                finally:
                    self.order_lock.release()
            
            result = await _create_order_with_lock()
            
            # result is a tuple: (tx, tx_hash, error)
            tx, tx_hash, err = result
            
            if err:
                print(f"⚠️  Order placement error: {err}")
                print(f"   📋 Order details: {side_str} {size:.4f} {symbol} @ ${price:.4f}, is_closing={is_closing}")
                # Revert estimated position
                with self.state_lock:
                    current = self.open_positions_est.get(market_index, 0.0)
                    delta = size if is_buy else -size
                    self.open_positions_est[market_index] = current - delta
            else:
                print(f"✅ Order placed successfully")
                # V1.9.4: Store the tag for this position (only for opens, not closes)
                if not is_closing:
                    with self.state_lock:
                        self.position_tags[market_index] = tagged_client_order_index

        except Exception as e:
            print(f"❌ Order failed (async): {e}")
            print(f"   📋 Order: {side_str} {size:.4f} {symbol} @ ${price:.4f}, is_closing={is_closing}")
            print(f"   🔍 Exception type: {type(e).__name__}")
            import traceback
            traceback.print_exc()
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
            
            # Get both bid and ask for fallback logic
            best_bid = None
            best_ask = None
            
            if hasattr(order_book, 'bids') and order_book.bids:
                best_bid = float(order_book.bids[0].price)
            
            if hasattr(order_book, 'asks') and order_book.asks:
                best_ask = float(order_book.asks[0].price)
            
            # Primary: use the side we need
            if is_buy:
                if best_ask:
                    return best_ask
                # Fallback: use bid if ask missing
                if best_bid:
                    return best_bid
            else:
                if best_bid:
                    return best_bid
                # Fallback: use ask if bid missing
                if best_ask:
                    return best_ask
            
            # Last resort: mid-price
            if best_bid and best_ask:
                return (best_bid + best_ask) / 2.0
            
            return None
                
        except Exception as e:
            # Silent - caller will handle
            return None
    
    def _get_market_price(self, market_index, is_buy):
        """Get current market price for a market (wrapper for thread)"""
        if not self.order_api:
            return None
        
        if not self.main_loop:
            return None
        
        try:
            if self.main_loop.is_running():
                future = asyncio.run_coroutine_threadsafe(
                    self._get_market_price_async(market_index, is_buy),
                    self.main_loop
                )
                result = future.result(timeout=5)
                return result
            else:
                return None
        except asyncio.TimeoutError:
            return None
        except Exception as e:
            return None

    def _apply_our_fill_to_positions(self, fill):
        """
        Update our position tracking when we get filled.
        
        Features:
        1. Coalesce multiple fills into one log (wait 500ms)
        2. Calculate and display slippage %
        3. Track PnL and log when position closes
        4. V1.9.7: Extract and store the bot tag for position tagging
        5. Multi-bot: Only process fills with our BOT_TAG (ignore other bots' fills)
        """
        try:
            market_index = fill.get('market_id')
            if market_index is None:
                return

            size = float(fill.get('size', 0))
            price = float(fill.get('price', 0))
            ask_account_id = fill.get('ask_account_id')
            bid_account_id = fill.get('bid_account_id')

            # Determine which side of the trade is OURS first - the tag lives on
            # that side's client id.
            if ask_account_id == self.our_account_index:
                delta = -size  # SELL
                side = 'SELL'
                # V1.9.7: Lighter Trade JSON exposes ask_client_id / bid_client_id,
                # NOT a 'client_order_index' field. Read the tag from our side.
                raw_tag = fill.get('ask_client_id', fill.get('ask_client_id_str', 0))
            elif bid_account_id == self.our_account_index:
                delta = size  # BUY
                side = 'BUY'
                raw_tag = fill.get('bid_client_id', fill.get('bid_client_id_str', 0))
            else:
                return

            # Normalize tag to int (the _str variants are strings; front-end / untagged
            # orders report 0).
            try:
                client_order_index = int(raw_tag or 0)
            except (TypeError, ValueError):
                client_order_index = 0

            # Multi-bot protection: CRITICAL
            # If the fill carries a tag from a DIFFERENT bot's band, ignore it so this
            # bot never tracks or later closes another bot's position.
            # A tag of 0 means untagged (e.g. orphan close with cid=0, manual trade, or
            # a front-end fill) - we still apply it to our position math but it will not
            # be claimed as owned by this bot in position_tags.
            if client_order_index > 0:
                if client_order_index < self.BOT_TAG or client_order_index >= self.BOT_TAG + self.TAG_WIDTH:
                    # This fill belongs to a different bot's band - skip it.
                    return

            # Add fill to pending buffer for coalescing
            self._add_fill_to_buffer(market_index, delta, price, side, fill, client_order_index)

        except Exception as e:
            print(f"⚠️  Error applying our fill: {e}")
    
    def _add_fill_to_buffer(self, market_index, delta, price, side, fill, client_order_index):
        """Add fill to buffer and start/reset timer for coalescing (V1.9.4: with tag tracking)"""
        with self.state_lock:
            if market_index not in self.pending_fills:
                # Snapshot the CURRENT position before any fill is applied.
                # This is the only correct baseline for close_ratio in PnL calculations.
                # V1.9.8 FIX: In multi-bot mode we must snapshot THIS bot's own CONFIRMED
                # position (open_positions_confirmed), NOT open_positions_est. The estimate
                # is bumped optimistically at order placement time (_place_order_internal),
                # BEFORE this fill arrives — so by the time we get here, open_positions_est
                # already includes this very fill's delta. Using it as "before" would double
                # -count the delta (once at placement, once here), inflating the confirmed
                # position to roughly 2x its real size.
                if self.multi_bot_mode:
                    position_before = self.open_positions_confirmed.get(market_index, 0.0)
                else:
                    position_before = self.open_positions.get(market_index, 0.0)
                self.pending_fills[market_index] = {
                    'total_size': 0,
                    'total_cost': 0,
                    'fills': [],
                    'side': side,
                    'timer': None,
                    'timestamp': fill.get('timestamp', time.time() * 1000),
                    'client_order_index': client_order_index,  # V1.9.4: Store tag
                    'position_before': position_before,        # Snapshot for PnL
                }
            
            # Add this fill
            self.pending_fills[market_index]['total_size'] += abs(delta)
            self.pending_fills[market_index]['total_cost'] += abs(delta) * price
            self.pending_fills[market_index]['fills'].append(fill)
            
            # V1.9.4: Update client_order_index if this fill has one
            if client_order_index > 0:
                self.pending_fills[market_index]['client_order_index'] = client_order_index
            
            # Cancel existing timer if any
            if self.pending_fills[market_index]['timer']:
                self.pending_fills[market_index]['timer'].cancel()
            
            # Start new timer to flush after window
            timer = threading.Timer(
                self.fill_coalesce_window_sec,
                self._flush_pending_fills,
                args=[market_index]
            )
            timer.daemon = True
            timer.start()
            self.pending_fills[market_index]['timer'] = timer
    
    def _flush_pending_fills(self, market_index):
        """
        Flush pending fills for this market and log aggregated result.
        
        Calculates:
        - Total size
        - Weighted average price
        - Slippage vs intended price
        - PnL if position closed
        """
        with self.state_lock:
            if market_index not in self.pending_fills:
                return
            
            buffer = self.pending_fills.pop(market_index)
            
            total_size = buffer['total_size']
            total_cost = buffer['total_cost']
            side = buffer['side']
            fills = buffer['fills']
            client_order_index = buffer.get('client_order_index', 0)  # V1.9.4: Extract tag
            # Use the position snapshot taken at first-fill time, not the current
            # open_positions value which may have been updated by subsequent flushes.
            # V1.9.8 FIX: track against THIS bot's own CONFIRMED position
            # (open_positions_confirmed), never open_positions_est. The estimate is
            # bumped optimistically at order placement, so using it here would apply
            # this fill's delta a second time on top of the placement-time bump.
            if self.multi_bot_mode:
                current = buffer.get('position_before',
                                     self.open_positions_confirmed.get(market_index, 0.0))
            else:
                current = buffer.get('position_before',
                                     self.open_positions.get(market_index, 0.0))

            if total_size == 0:
                return
            
            # Calculate weighted average fill price
            avg_price = total_cost / total_size
            
            # current = position BEFORE this batch of fills (captured at first fill time)
            # new_pos = what the real position will be after this batch
            delta = total_size if side == 'BUY' else -total_size
            # V1.9.8 FIX: base new_pos on the CONFIRMED position, not the optimistic
            # estimate, for the same double-counting reason as above.
            if self.multi_bot_mode:
                actual_current = self.open_positions_confirmed.get(market_index, 0.0)
            else:
                actual_current = self.open_positions.get(market_index, 0.0)
            new_pos = actual_current + delta
            
            # V1.9.8 FIX: split this batch into a CLOSING portion (bounded by the
            # position that existed before it) and an OPENING portion (any remainder).
            # A remainder occurs on a "flip": two of our own orders (e.g. one closing
            # a LONG, one opening a SHORT immediately after) can coalesce into the SAME
            # buffer if their fills land within the coalescing window. Previously,
            # close_ratio = total_size / abs(current) could then exceed 1.0, consuming
            # MORE than the actual entry cost and driving trade_entry_costs negative —
            # silently corrupting every PnL calculation on that market from then on.
            # Splitting bounds close_ratio at exactly 1.0 and correctly opens a fresh
            # cost basis for the flip remainder.
            if current == 0:
                closing_size, opening_size = 0.0, abs(delta)
            elif (current > 0 and delta < 0) or (current < 0 and delta > 0):
                reducing = min(abs(delta), abs(current))
                closing_size = reducing
                opening_size = abs(delta) - reducing  # > 0 only on a flip
            else:
                closing_size, opening_size = 0.0, abs(delta)
            
            is_opening = opening_size > 1e-12
            is_closing = closing_size > 1e-12
            is_flip = is_opening and is_closing
            
            # Sur chaque close : calculer closed_entry_cost et réduire entry_cost
            # (must run BEFORE the opening block so a flip's remainder starts from the
            # correctly-zeroed cost basis left behind by fully closing the prior side)
            closed_entry_cost = 0.0
            if is_closing:
                entry_cost = self.trade_entry_costs.get(market_index, 0)
                if entry_cost > 0 and abs(current) > 1e-8:
                    close_ratio = closing_size / abs(current)  # now guaranteed <= 1.0
                    closed_entry_cost = entry_cost * close_ratio
                    self.trade_entry_costs[market_index] = entry_cost - closed_entry_cost
            
            if is_opening:
                # Opening or adding to position - update entry cost
                opening_cost = opening_size * avg_price
                old_cost = self.trade_entry_costs.get(market_index, 0)
                new_cost = old_cost + opening_cost
                self.trade_entry_costs[market_index] = new_cost
                denom = abs(new_pos) if abs(new_pos) > 1e-12 else opening_size
                self.trade_entry_prices[market_index] = new_cost / denom if denom > 0 else avg_price
                
                # V1.9.4: Store the tag for this position (for orphan detection)
                if client_order_index > 0:
                    self.position_tags[market_index] = client_order_index

            # Clean up positions very close to zero
            position_closed = False
            if abs(new_pos) < 1e-8:
                # V1.9.8: In multi-bot mode, open_positions is the shared account net
                # owned by the API sync — don't pop it here, only clear our own tracking.
                if not self.multi_bot_mode:
                    self.open_positions.pop(market_index, None)
                # V1.9.8 FIX: new_pos is the CONFIRMED truth (derived from
                # open_positions_confirmed + this fill's delta) — reset the estimate to
                # match it, correcting any optimistic drift, exactly like single-bot mode
                # already does relative to open_positions.
                self.open_positions_confirmed.pop(market_index, None)
                self.open_positions_est.pop(market_index, None)
                self.position_tags.pop(market_index, None)  # V1.9.4: Clean up tag
                self.orphan_close_attempts.pop(market_index, None)  # V1.9.8: reset loop guard
                position_closed = True
            else:
                # V1.9.8: In multi-bot mode, don't overwrite the shared account net.
                if not self.multi_bot_mode:
                    self.open_positions[market_index] = new_pos
                # V1.9.8 FIX: new_pos is confirmed truth; store it as such, then reset
                # the optimistic estimate to match it (clears any placement-time drift).
                self.open_positions_confirmed[market_index] = new_pos
                self.open_positions_est[market_index] = new_pos
                # V1.9.8: a real fill moved our estimate — reset the loop guard so a
                # legitimate future orphan gets full retries again.
                self.orphan_close_attempts.pop(market_index, None)
            
            # Track last observed price for market orders
            self.last_observed_prices[market_index] = avg_price
            
            # Get target fill timestamp for latency calculation
            target_fill_ts = self.order_target_timestamps.pop(market_index, None)
            intended_price = self.order_intended_prices.pop(market_index, None)

        # Now log everything (outside lock)
        symbol = self._get_market_symbol(market_index)
        market_meta = self.market_metadata.get(market_index, {})
        price_decimals = market_meta.get('price_decimals', 2)
        
        # Calculate latency if we have the target timestamp
        latency_str = ""
        if target_fill_ts:
            our_fill_ts = int(fills[0].get('timestamp', time.time() * 1000))
            latency_ms = our_fill_ts - target_fill_ts
            latency_str = f" | latency={latency_ms}ms"
        
        # Calculate slippage vs prix du target
        # Convention: négatif = on a été fillé moins bien que le target
        #   BUY:  on a payé plus cher que target → négatif
        #   SELL: on a vendu moins cher que target → négatif
        slippage_str = ""
        if intended_price and intended_price > 0:
            if side == 'BUY':
                slippage_pct = ((intended_price - avg_price) / intended_price) * 100
            else:  # SELL
                slippage_pct = ((avg_price - intended_price) / intended_price) * 100
            
            # Only show if slippage is significant (>0.01%)
            if abs(slippage_pct) > 0.01:
                sign = "+" if slippage_pct > 0 else ""
                slippage_str = f" (slippage {sign}{slippage_pct:.2f}%)"
        
        # For now, just show the fill
        fills_count = len(fills)
        if fills_count > 1:
            print(f"✅ Our fill: {side} {total_size:.4f} {symbol} @ ${avg_price:.{price_decimals}f}{slippage_str} ({fills_count} fills){latency_str}")
        else:
            print(f"✅ Our fill: {side} {total_size:.4f} {symbol} @ ${avg_price:.{price_decimals}f}{slippage_str}{latency_str}")
        
        # V1.9.8: note when this batch was a flip (closed one side, opened the other)
        if is_flip:
            new_side = 'LONG' if new_pos > 0 else 'SHORT'
            print(f"   🔀 Flip detected: closed prior position, opened new {new_side} "
                  f"{abs(new_pos):.4f} {symbol}")

        # Log PnL sur chaque close (partiel ou total)
        # closed_entry_cost a été calculé dans le bloc is_closing (dans la lock)
        if is_closing and closed_entry_cost > 0:
            # V1.9.8 FIX: exit_value must reflect ONLY the closing portion of this
            # batch, at this batch's weighted avg price. Using total_cost here (the
            # old behavior) was wrong whenever the batch also contained an opening
            # portion (a flip), since total_cost covers the full batch size.
            exit_value = closing_size * avg_price

            if current > 0:  # Was LONG: PnL = exit - entry
                our_pnl = exit_value - closed_entry_cost
            else:  # Was SHORT: PnL = entry - exit
                our_pnl = closed_entry_cost - exit_value

            pnl_sign = "+" if our_pnl >= 0 else ""

            # V1.9.8 REWRITE: target PnL is no longer derived from a cost ratio
            # (which mixed our own dollar scale with the target's and was never
            # dimensionally meaningful). Instead we consume the exact dollar PnL
            # the target realized on the closes that triggered our copy order(s)
            # in this batch, queued in pending_target_close_pnl by _process_target_fill.
            target_pnl_str = ""
            with self.state_lock:
                target_pnl = self.pending_target_close_pnl.pop(market_index, None)
            if target_pnl is not None:
                t_sign = "+" if target_pnl >= 0 else ""
                pct_vs_target = (our_pnl / target_pnl * 100) if abs(target_pnl) > 1e-6 else 0
                target_pnl_str = f" | target: {t_sign}${target_pnl:.2f} ({pct_vs_target:.0f}%)"

            if position_closed:
                print(f"   💰 Position CLOSED: PnL {pnl_sign}${our_pnl:.2f}{target_pnl_str}")
                # Clean up OUR OWN trackers only. Target-side trackers follow the
                # TARGET's own position lifecycle (handled independently in
                # _process_target_fill when the target itself goes flat) — they must
                # NOT be wiped here, since the target can still hold an open remainder
                # even after OUR position is fully closed (rounding, coin filters,
                # missed fills, etc.). Wiping them here would corrupt the target's own
                # still-open cost basis.
                self.trade_entry_prices.pop(market_index, None)
                self.trade_entry_costs.pop(market_index, None)
            else:
                print(f"   💰 Partial close PnL: {pnl_sign}${our_pnl:.2f}{target_pnl_str} (pos restante: {abs(new_pos):.4f})") 

    # ------------------------
    # Emergency flatten
    # ------------------------
    def emergency_flatten_all_positions(self):
        """
        Emergency flatten all positions using MARKET orders.
        
        Uses market orders (not limit) to ensure positions actually close
        during disconnection, even in fast-moving markets.
        """
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

            print(f"🚨 SAFETY: Flattening {len(positions)} position(s) with MARKET orders...")
            for market_index, pos in positions.items():
                if abs(pos) < 1e-8:
                    continue
                
                is_buy = pos < 0  # If SHORT, we BUY to close
                size = abs(pos)
                symbol = self._get_market_symbol(market_index)
                
                try:
                    # Use market order for orphan close (guarantees fill)
                    self._place_market_order_for_orphan(market_index, is_buy, size, symbol)
                except Exception as e:
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
                if self.disconnect_start_time is None:
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
                    if self.disconnect_start_time is not None:
                        elapsed = time.time() - self.disconnect_start_time
                        print(f"✅ Reconnected after {elapsed:.0f}s outage")
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
                # Only log on first disconnect to avoid flooding
                if self.disconnect_start_time is None:
                    e_str = str(e)
                    code = next((c for c in ['500', '502', '503', '504'] if c in e_str), None)
                    if code:
                        print(f"❌ WebSocket error: HTTP {code} - server unavailable")
                    else:
                        print(f"❌ WebSocket error: {e_str[:100]}")
                    print(f"🔁 Reconnecting every {self.reconnect_delay_sec}s until service recovers...")

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
