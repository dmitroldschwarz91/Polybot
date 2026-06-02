#!/usr/bin/env python3
"""
Polymarket 5-min crypto bot (UP/DOWN)
Version: 5.7.3 -- Binance start price + Direct WS

Fixes:
- [BUG-1] Fixed Vacuum Scalp entry window overlap with Standard Entry
- [BUG-2] Added TP order timeout/expiry handling
- [BUG-3] Fixed double proceeds accounting for Vacuum TP
- [BUG-4] Added stale book check for Vacuum Scalp
- [PERF-1] Optimized get_volatility with cached min/max
- [LOGIC-1] Handle EXPIRED positions with actual PnL calculation
- [PRIORITY-1] check_and_handle_urgent_sl() — pre-entry SL guard
- [PRIORITY-2] _check_sl_inline() — SL monitoring DURING wait_for_fill
  → SL checked every 50ms even while waiting for buy order fill
  → Zero gaps in SL coverage regardless of buy duration
- [LOGIC-2] Added orderbook liquidity (asks) check before High Price Entry
"""

import os, re, io, sys, json, time, asyncio, logging, aiohttp, requests, urllib3, websockets
from functools import partial as fp
from datetime import datetime, timezone
from logging.handlers import RotatingFileHandler
from requests.adapters import HTTPAdapter
from decimal import Decimal, ROUND_DOWN, ROUND_FLOOR, InvalidOperation
from collections import deque
from dataclasses import dataclass, field
from typing import Optional, Dict, List, Any, Tuple, Set, Deque
from enum import Enum

from dotenv import load_dotenv
from py_clob_client_v2 import (
    ClobClient, OrderArgs, MarketOrderArgs, OrderType, Side,
    PartialCreateOrderOptions, BalanceAllowanceParams, AssetType
)
load_dotenv()

HAS_FAK = hasattr(OrderType, 'FAK')
if not HAS_FAK:
    logging.getLogger("polybot").warning(
        "OrderType.FAK not available in py_clob_client_v2. Will use FOK as fallback. "
        "Update: pip install --upgrade py_clob_client_v2"
    )

# ═══════════════════════════════════════════════════════════════════════════
# CONFIG
# ═══════════════════════════════════════════════════════════════════════════

PRIVATE_KEY = os.getenv("POLYMARKET_PRIVATE_KEY", "YOUR_KEY")
FUNDER_ADDRESS = os.getenv("POLYMARKET_FUNDER_ADDRESS", "YOUR_ADDRESS")
SIGNATURE_TYPE = 1; INITIAL_BALANCE = 7.0; ASSETS = ["BTC", "ETH"]
INTERVAL_MINUTES = 5; POLL_INTERVAL = 0.1
STANDARD_ENTRY_ENABLED = False
ENTRY_WINDOW_SECS = 11; EARLY_TREND_CUTOFF_SECS = 120; EARLY_TREND_ENABLED = False
MIN_LOT_PRICE = 0.89; HIGH_PRICE_THRESHOLD = 0.97
EARLY_TREND_MIN_PRICE = 0.75; EARLY_TREND_MAX_PRICE = 0.90; EARLY_TREND_MAX_SPREAD = 0.03
MIN_ORDER_SIZE = 1
MIN_ORDER_VALUE = 1.0
PRICE_HIST_WINDOW = 10; MIN_TREND_DIFF = 0.005; MIN_CONFIDENCE = 0.3
MAX_CV = 0.1; MAX_DIRECTION_CHANGES = 4; MIN_PRICE_POINTS = 3
DEQUE_MAXLEN = 300

STANDARD_BUY_PRICE = 0.99
NUCLEAR_CRASH_PCT = 0.15
NUCLEAR_SELL_PRICE = 0.01
FILL_ANOMALY_PCT = 0.20
SL_DYNAMIC_SLIPPAGE_PCT = 0.03
SL_CHASE_TIMEOUT = 2.0
SL_CHASE_STEP_PCT = 0.02
SL_MAX_CHASE_ROUNDS = 3
FALLBACK_CONFIDENCE_MULTIPLIER = 0.7; EARLY_TREND_MIN_DEVIATION = 0.001
EARLY_TREND_MAX_STAKE_RATIO = 0.30; MAX_STAKE_RATIO = 0.75
EARLY_TREND_TP_PCT = 0.05; EARLY_TREND_PARTIAL_TP_RATIO = 0.5; EARLY_TREND_SL_PCT = 0.10
TRAILING_STOP_DISTANCE_PCT = 0.03; TRAILING_STOP_MIN_PROFIT_PCT = 0.02; STANDARD_SL_PCT = 0.10
EARLY_TREND_MICRO_WINDOW = 10.0; EARLY_TREND_MICRO_MIN_POINTS = 3; EARLY_TREND_MICRO_MIN_CHANGE_PCT = 0.0001
IMBALANCE_ENABLED = True; VACUUM_IMBALANCE_THRESHOLD = 0.95; HIGH_IMBALANCE_THRESHOLD = 0.85; MODERATE_IMBALANCE_THRESHOLD = 0.70
WS_BOOK_STALE_SECS = 30
IMBALANCE_STAKE_MULTIPLIERS = {0.95:1.3, 0.90:1.25, 0.85:1.2, 0.80:1.1}
IMBALANCE_CONFIDENCE_BOOST = {0.95:0.20, 0.90:0.15, 0.85:0.10, 0.80:0.05}
EARLY_EXIT_ENABLED = True; EARLY_EXIT_WINDOW = 5
EARLY_EXIT_MIN_PROFIT = 0.01
EARLY_EXIT_SKIP_ABOVE_PRICE = 0.98
SNAPSHOT_BEFORE_END = 15; BALANCE_LOG_INTERVAL = 60
MONITOR_INTERVAL = 0.1
MONITOR_GRACE_PERIOD = 5.0; HTTP_TIMEOUT = (5, 10); HTTP_RETRIES = 3; BALANCE_SAFETY_MARGIN = 0.98
QUIET_MODE = True

# ═══════════════════════════════════════════════════════════════════════════
# v5.7.2.1: VACUUM SCALP STRATEGY CONFIG (FIXED)
# ═══════════════════════════════════════════════════════════════════════════
VACUUM_SCALP_ENABLED = True
VACUUM_SCALP_ENTRY_START_SECS = 150      # [FIX] Changed from 180 to avoid gap with Early Trend
VACUUM_SCALP_ENTRY_END_SECS = 30
VACUUM_SCALP_MIN_DEVIATION = 0.001
VACUUM_SCALP_MIN_TOKEN_PRICE = 0.95
VACUUM_SCALP_MAX_TOKEN_PRICE = 0.98
VACUUM_SCALP_MAX_VOLATILITY = 0.0002
VACUUM_SCALP_VOLATILITY_WINDOW = 10.0
VACUUM_SCALP_LIQUIDITY_RATIO = 10.0
VACUUM_SCALP_TP_DELTA = 0.02
VACUUM_SCALP_SL_PCT = 0.10
VACUUM_SCALP_MAX_STAKE_RATIO = 0.72
VACUUM_SCALP_BOOK_MAX_AGE = 5.0          # [NEW] Max book age for vacuum scalp (stricter)
VACUUM_SCALP_TP_TIMEOUT_SECS = 60.0      # [NEW] Cancel TP if not filled after 60s
START_PRICE_CHAINLINK_GRACE_SECS = 1.5   # сколько ждём boundary price от Chainlink
START_PRICE_CHAINLINK_POLL_SECS = 0.05   # шаг повторной проверки
_vacuum_diag_last_log: Dict[str, float] = {}

WS_RTDS_URL = "wss://ws-live-data.polymarket.com"
WS_MARKET_URL = "wss://ws-subscriptions-clob.polymarket.com/ws/market"
WS_USER_URL = "wss://ws-subscriptions-clob.polymarket.com/ws/user"
WS_HEARTBEAT_INTERVAL = 5; WS_RECONNECT_DELAY = 2
BUY_FILL_TIMEOUT_EARLY = 3.0
BUY_FILL_TIMEOUT_STANDARD = 1.0
BUY_FILL_TIMEOUT_VACUUM = 2.0
FILL_WAIT_INTERVAL = 0.05
CHAINLINK_SYMBOLS = {"BTC": "btc/usd", "ETH": "eth/usd"}
BINANCE_SYMBOLS_WS = {"BTC": "btcusdt", "ETH": "ethusdt"}
BINANCE_API = "https://api.binance.com/api/v3"
GAMMA_API = "https://gamma-api.polymarket.com"
CLOB_API = "https://clob.polymarket.com"
BINANCE_WS_DIRECT = "wss://stream.binance.com:9443/ws"
BINANCE_STREAMS = ["btcusdt@aggTrade", "ethusdt@aggTrade"]
CHAIN_ID_POLYGON = 137
PRICE_PATTERN = re.compile(r'\$([0-9,]+\.?[0-9]*)')


# ═══════════════════════════════════════════════════════════════════════════
# ENUMS & DATACLASSES
# ═══════════════════════════════════════════════════════════════════════════

class EntryType(Enum):
    STANDARD = "STANDARD"
    EARLY_TREND = "EARLY_TREND"
    HIGH_PRICE = "HIGH_PRICE"
    IMBALANCE = "IMBALANCE"
    VACUUM_SCALP = "VACUUM_SCALP"

class CloseReason(Enum):
    TAKE_PROFIT = "take_profit"
    PARTIAL_TP = "partial_tp"
    TRAILING_STOP = "trailing_stop"
    STOP_LOSS = "stop_loss"
    EARLY_EXIT = "early_exit"
    EXPIRED = "expired"
    VACUUM_TP = "vacuum_tp"

@dataclass
class Position:
    slug: str
    asset: str
    token_id: str
    direction: str
    entry_price: float
    entry_size: int
    entry_cost: float
    entry_type: EntryType = EntryType.STANDARD
    entry_timestamp: float = field(default_factory=time.time)
    order_id: Optional[str] = None
    current_size: int = 0
    end_ts: int = 0
    take_profit_price: float = 0.0
    stop_loss_price: float = 0.0
    partial_tp_taken: bool = False
    trailing_active: bool = False
    max_price_seen: float = 0.0
    trailing_stop_price: float = 0.0
    partial_tp_pnl: float = 0.0
    partial_tp_size: int = 0
    real_cost: float = 0.0
    order_locked_cost: float = 0.0
    confidence: float = 0.0
    target_price: Optional[float] = None
    entry_deviation: Optional[float] = None
    closed: bool = False
    close_reason: Optional[CloseReason] = None
    close_pnl: float = 0.0
    close_proceeds: float = 0.0
    close_timestamp: Optional[float] = None
    sl_in_progress: bool = False
    tp_order_id: Optional[str] = None
    tp_order_placed: bool = False
    tp_order_timestamp: float = 0.0  # [NEW] Track when TP order was placed
    tp_pending_priority: bool = False

    def __post_init__(self):
        if self.current_size == 0:
            self.current_size = self.entry_size
        if self.max_price_seen == 0:
            self.max_price_seen = self.entry_price
        if self.real_cost == 0:
            self.real_cost = self.entry_cost

    @property
    def total_pnl(self):
        return self.partial_tp_pnl + self.close_pnl

    def update_trailing(self, cp):
        if not self.trailing_active or cp <= self.max_price_seen:
            return False
        self.max_price_seen = cp
        nt = max(cp * (1 - TRAILING_STOP_DISTANCE_PCT), self.entry_price * (1 + TRAILING_STOP_MIN_PROFIT_PCT))
        if nt > self.trailing_stop_price:
            self.trailing_stop_price = nt
            return True
        return False

    def record_partial_tp(self, size, pnl, trailing):
        self.partial_tp_taken = True
        self.partial_tp_pnl = pnl
        self.partial_tp_size = size
        self.current_size -= size
        self.trailing_active = True
        self.trailing_stop_price = trailing

    def record_close(self, reason, pnl, proceeds=0.0):
        self.closed = True
        self.close_reason = reason
        self.close_pnl = pnl
        self.close_proceeds = proceeds
        self.close_timestamp = time.time()
        self.current_size = 0


@dataclass
class TradeStats:
    early_trend_count: int = 0
    early_trend_wins: int = 0
    early_trend_losses: int = 0
    early_trend_pnl: float = 0.0
    standard_count: int = 0
    standard_wins: int = 0
    standard_losses: int = 0
    standard_pnl: float = 0.0
    vacuum_scalp_count: int = 0
    vacuum_scalp_wins: int = 0
    vacuum_scalp_losses: int = 0
    vacuum_scalp_pnl: float = 0.0
    partial_tps: int = 0
    trailing_exits: int = 0
    stop_losses: int = 0
    early_exits: int = 0
    vacuum_tps: int = 0
    expired_count: int = 0  # [NEW] Track expired positions

    @property
    def total_trades(self):
        return self.early_trend_count + self.standard_count + self.vacuum_scalp_count

    @property
    def total_pnl(self):
        return self.early_trend_pnl + self.standard_pnl + self.vacuum_scalp_pnl

    @property
    def win_rate(self):
        w = self.early_trend_wins + self.standard_wins + self.vacuum_scalp_wins
        return w / self.total_trades if self.total_trades else 0.0

    def record(self, pnl, et, reason):
        if et == EntryType.EARLY_TREND:
            self.early_trend_count += 1
            self.early_trend_pnl += pnl
            if pnl > 0:
                self.early_trend_wins += 1
            elif pnl < 0:
                self.early_trend_losses += 1
        elif et == EntryType.VACUUM_SCALP:
            self.vacuum_scalp_count += 1
            self.vacuum_scalp_pnl += pnl
            if pnl > 0:
                self.vacuum_scalp_wins += 1
            elif pnl < 0:
                self.vacuum_scalp_losses += 1
        else:
            self.standard_count += 1
            self.standard_pnl += pnl
            if pnl > 0:
                self.standard_wins += 1
            elif pnl < 0:
                self.standard_losses += 1

        if reason == CloseReason.TRAILING_STOP:
            self.trailing_exits += 1
        elif reason == CloseReason.STOP_LOSS:
            self.stop_losses += 1
        elif reason == CloseReason.EARLY_EXIT:
            self.early_exits += 1
        elif reason == CloseReason.PARTIAL_TP:
            self.partial_tps += 1
        elif reason == CloseReason.VACUUM_TP:
            self.vacuum_tps += 1
        elif reason == CloseReason.EXPIRED:
            self.expired_count += 1


@dataclass
class BalanceState:
    prev_wallet_usdc: Optional[float] = None
    prev_bot_snap: float = INITIAL_BALANCE
    total_profit: float = 0.0
    intervals_passed: int = 0


# ═══════════════════════════════════════════════════════════════════════════
# FILL STORE
# ═══════════════════════════════════════════════════════════════════════════

class FillStore:
    def __init__(self):
        self.orders: Dict[str, Dict[str, Any]] = {}

    def _ensure(self, order_id: str) -> Dict[str, Any]:
        if order_id not in self.orders:
            self.orders[order_id] = {
                "status": None, "side": None, "limit_price": 0.0,
                "original_size": 0.0, "size_matched": 0.0,
                "filled_size": 0.0, "filled_value": 0.0,
                "avg_fill_price": 0.0, "last_ts": 0.0,
            }
        return self.orders[order_id]

    def record_order_event(self, order_id: str, side: str, limit_price: float,
                           original_size: float, size_matched: float, status: str):
        rec = self._ensure(order_id)
        rec["side"] = side or rec["side"]
        if limit_price > 0:
            rec["limit_price"] = limit_price
        if original_size > 0:
            rec["original_size"] = original_size
        if size_matched >= 0:
            rec["size_matched"] = size_matched
        rec["status"] = status or rec["status"]
        rec["last_ts"] = time.time()

    def record_trade_event(self, order_id: str, side: str, price: float, size: float):
        rec = self._ensure(order_id)
        rec["side"] = side or rec["side"]
        rec["filled_size"] += size
        rec["filled_value"] += price * size
        if rec["filled_size"] > 0:
            rec["avg_fill_price"] = rec["filled_value"] / rec["filled_size"]
        rec["last_ts"] = time.time()

    def snapshot(self, order_id: str) -> Optional[Dict[str, Any]]:
        rec = self.orders.get(order_id)
        if not rec:
            return None
        return dict(rec)

    def is_filled(self, order_id: str) -> bool:
        rec = self.orders.get(order_id)
        if not rec:
            return False
        status = (rec.get("status") or "").upper()
        if status in ("FILLED", "MATCHED"):
            return True
        orig = rec.get("original_size", 0)
        matched = max(rec.get("filled_size", 0), rec.get("size_matched", 0))
        return orig > 0 and matched >= orig

    def get_filled_size(self, order_id: str) -> float:
        """[NEW] Get actual filled size for partial fills."""
        rec = self.orders.get(order_id)
        if not rec:
            return 0.0
        return max(rec.get("filled_size", 0), rec.get("size_matched", 0))


fills = FillStore()
_api_creds: Optional[Dict[str, str]] = None
_gamma_cache: Dict[str, Tuple[Optional[Dict], float]] = {}
_interval_start_prices: Dict[str, Dict[str, float]] = {}
GAMMA_CACHE_TTL = 2.0


# ═══════════════════════════════════════════════════════════════════════════
# LIVE PRICE STORE (with optimized volatility)
# ═══════════════════════════════════════════════════════════════════════════

class LivePriceStore:
    def __init__(self):
        self.chainlink: Dict[str, float] = {}
        self.chainlink_ts: Dict[str, float] = {}
        self.chainlink_history: Dict[str, Deque] = {a: deque(maxlen=600) for a in ASSETS}
        self.binance: Dict[str, float] = {}
        self.binance_ts: Dict[str, float] = {}
        self.binance_history: Dict[str, Deque] = {a: deque(maxlen=600) for a in ASSETS}
        self.binance_direct: Dict[str, float] = {}      # Новый источник
        self.binance_direct_ts: Dict[str, float] = {}
        self.binance_direct_history: Dict[str, Deque] = {a: deque(maxlen=600) for a in ASSETS}
        self.books: Dict[str, Dict] = {}
        self.lot_prices: Dict[str, float] = {}
        self.lot_prices_ts: Dict[str, float] = {}
        # [PERF-1] Volatility cache
        self._volatility_cache: Dict[str, Tuple[float, float]] = {}  # {asset: (volatility, timestamp)}
        self._volatility_cache_ttl = 0.5  # 500ms cache

    def update_chainlink(self, asset, price, oracle_ts_ms=None):
        now = time.time()
        self.chainlink[asset] = price
        self.chainlink_ts[asset] = now
        ots = oracle_ts_ms if oracle_ts_ms is not None else int(now * 1000)
        self.chainlink_history[asset].append((ots, now, price))  # (oracle_ms, local_ts, price)
        self._volatility_cache.pop(asset, None)  # Invalidate cache

    def update_binance(self, asset, price):
        now = time.time()
        self.binance[asset] = price
        self.binance_ts[asset] = now
        self.binance_history[asset].append((now, price))
        self._volatility_cache.pop(asset, None)  # Invalidate cache

    def update_binance_direct(self, asset, price):
        now = time.time()
        self.binance_direct[asset] = price
        self.binance_direct_ts[asset] = now
        self.binance_direct_history[asset].append((now, price))
        # Инвалидируем кеш волатильности
        self._volatility_cache.pop(asset, None)

    def update_lot_price(self, token_id, best_ask, best_bid=None):
        now = time.time()
        if best_ask is not None and best_ask > 0:
            self.lot_prices[token_id] = best_ask
            self.lot_prices_ts[token_id] = now
        if token_id not in self.books:
            self.books[token_id] = {
                "bids": [], "asks": [], "best_bid": None, "best_ask": None,
                "bid_volume": 0, "ask_volume": 0, "spread": None, "ts": 0
            }
        book = self.books[token_id]
        if best_ask is not None:
            book["best_ask"] = best_ask
        if best_bid is not None:
            book["best_bid"] = best_bid
        if book["best_ask"] and book["best_bid"]:
            book["spread"] = book["best_ask"] - book["best_bid"]
        book["ts"] = now

    def update_full_book(self, token_id, bids, asks):
        now = time.time()
        bb = float(bids[0]["price"]) if bids else None
        ba = float(asks[0]["price"]) if asks else None
        bid_vol = sum(float(b.get("size", 0)) for b in bids) if bids else 0
        ask_vol = sum(float(a.get("size", 0)) for a in asks) if asks else 0
        self.books[token_id] = {
            "bids": bids, "asks": asks, "best_bid": bb, "best_ask": ba,
            "bid_volume": bid_vol, "ask_volume": ask_vol,
            "spread": (ba - bb) if (ba and bb) else None, "ts": now
        }
        if ba and ba > 0:
            self.lot_prices[token_id] = ba
            self.lot_prices_ts[token_id] = now

    def get_oracle_price(self, asset):
        cl = self.chainlink.get(asset)
        if cl is not None:
            return cl
        bd = self.binance_direct.get(asset)
        if bd is not None:
            return bd
        
        return self.binance.get(asset)

    def get_fastest_price(self, asset) -> Tuple[Optional[float], str]:
        """Возвращает самую свежую цену и её источник."""
        now = time.time()
        sources = [
            (self.binance_direct.get(asset), self.binance_direct_ts.get(asset, 0), "binance_direct"),
            (self.chainlink.get(asset), self.chainlink_ts.get(asset, 0), "chainlink"),
            (self.binance.get(asset), self.binance_ts.get(asset, 0), "binance_rtds"),
        ]
        
        # Выбираем источник с самым свежим timestamp
        valid = [(p, ts, src) for p, ts, src in sources if p is not None and ts > 0]
        if not valid:
            return None, "none"
        
        best = max(valid, key=lambda x: x[1])
        return best[0], best[2]
        
    def get_lot_price(self, token_id):
        return self.lot_prices.get(token_id)

    def get_book(self, token_id) -> Optional[Dict]:
        b = self.books.get(token_id)
        if b and b.get("ts", 0) > 0:
            age = time.time() - b["ts"]
            if age < WS_BOOK_STALE_SECS:
                return b
            b["_stale"] = True
            return b
        return None

    def get_book_with_max_age(self, token_id, max_age: float) -> Optional[Dict]:
        """[NEW] Get book only if fresher than max_age seconds."""
        b = self.books.get(token_id)
        if b and b.get("ts", 0) > 0:
            age = time.time() - b["ts"]
            if age < max_age:
                return b
        return None

    def get_book_imbalance(self, token_id) -> float:
        b = self.get_book(token_id)
        if b is None:
            return 0.5
        bv = b.get("bid_volume", 0)
        av = b.get("ask_volume", 0)
        t = bv + av
        return bv / t if t > 0 else 0.5

    def get_chainlink_age(self, asset):
        ts = self.chainlink_ts.get(asset, 0)
        return time.time() - ts if ts > 0 else float('inf')

    def get_micro_trend_data(self, asset, ws=EARLY_TREND_MICRO_WINDOW):
        """Возвращает данные микро-тренда. Приоритет: binance_direct > binance_rtds"""
        cutoff = time.time() - ws
        
        # Приоритет: binance_direct (самый быстрый)
        history = self.binance_direct_history.get(asset)
        if history and len(history) >= EARLY_TREND_MICRO_MIN_POINTS:
            data = [(ts, p) for ts, p in history if ts >= cutoff]
            if len(data) >= EARLY_TREND_MICRO_MIN_POINTS:
                return data
        
        # Fallback на binance через RTDS
        return [(ts, p) for ts, p in self.binance_history.get(asset, []) if ts >= cutoff]

    def get_volatility(self, asset, window_secs=VACUUM_SCALP_VOLATILITY_WINDOW) -> Optional[float]:
        """[PERF-1] Optimized with caching. Supports 2-tuple and 3-tuple histories."""
        now = time.time()
        cached = self._volatility_cache.get(asset)
        if cached and (now - cached[1]) < self._volatility_cache_ttl:
            return cached[0]
            
        cutoff = now - window_secs
        
        # Приоритет источников: binance_direct → chainlink → binance_rtds
        history = self.binance_direct_history.get(asset)
        if not history or len(history) < 2:
            history = self.chainlink_history.get(asset)
        if not history or len(history) < 2:
            history = self.binance_history.get(asset)
        if not history or len(history) < 2:
            return None
            
        min_p = float('inf')
        max_p = float('-inf')
        count = 0

        for item in history:
            # Поддержка двух форматов:
            # 1) (ts_sec, price)
            # 2) (oracle_ts_ms, local_ts_sec, price)
            if len(item) == 2:
                ts, p = item
            elif len(item) == 3:
                _, ts, p = item   # используем local_ts_sec для окна волатильности
            else:
                continue

            if ts >= cutoff:
                if p < min_p:
                    min_p = p
                if p > max_p:
                    max_p = p
                count += 1

        if count < 2 or min_p <= 0:
            return None

        volatility = (max_p - min_p) / min_p
        self._volatility_cache[asset] = (volatility, now)
        return volatility


prices = LivePriceStore()


# ═══════════════════════════════════════════════════════════════════════════
# WEBSOCKET CONNECTIONS
# ═══════════════════════════════════════════════════════════════════════════

async def run_binance_direct_websocket():
    """Прямой WebSocket к Binance — быстрее, чем через RTDS."""
    streams = "/".join(BINANCE_STREAMS)
    url = f"{BINANCE_WS_DIRECT}/{streams}"
    
    while True:
        try:
            async with websockets.connect(url, ping_interval=20) as ws:
                log.info("[WS-BINANCE-DIRECT] Connected")
                async for raw in ws:
                    try:
                        msg = json.loads(raw)
                        symbol = msg.get("s", "").upper()  # "BTCUSDT"
                        price = float(msg.get("p", 0))     # Trade price
                        
                        if symbol == "BTCUSDT":
                            prices.update_binance_direct("BTC", price)
                        elif symbol == "ETHUSDT":
                            prices.update_binance_direct("ETH", price)
                    except Exception:
                        continue
        except Exception as e:
            log.warning("[WS-BINANCE-DIRECT] Reconnecting", error=str(e))
            await asyncio.sleep(1)


async def run_rtds_websocket():
    bn_symbols = list(BINANCE_SYMBOLS_WS.values())  # ["btcusdt", "ethusdt"]

    sub = json.dumps({
        "action": "subscribe",
        "subscriptions": [
            {"topic": "crypto_prices_chainlink", "type": "*", "filters": ""},
            {"topic": "crypto_prices", "type": "update", "filters": json.dumps(bn_symbols)}
        ]
    })

    while True:
        try:
            async with websockets.connect(WS_RTDS_URL, ping_interval=WS_HEARTBEAT_INTERVAL) as ws:
                await ws.send(sub)
                log.info("[WS-RTDS] Connected")

                async for raw in ws:
                    if raw == "PONG":
                        continue

                    try:
                        msg = json.loads(raw)

                        # Иногда сервер может прислать ошибку подписки/валидации
                        if isinstance(msg, dict):
                            body = msg.get("body")
                            if isinstance(body, dict) and body.get("statusCode"):
                                log.error("[WS-RTDS] Server error",
                                          status=body.get("statusCode"),
                                          message=body.get("message", ""))
                                continue

                        if not isinstance(msg, dict):
                            continue

                        topic = msg.get("topic", "")
                        payload = msg.get("payload")
                        if not isinstance(payload, dict):
                            continue

                        # ─────────────────────────────────────────────
                        # CHAINLINK FEED
                        # ─────────────────────────────────────────────
                        if topic == "crypto_prices_chainlink":
                            sym = (payload.get("symbol") or "").lower()
                            val = payload.get("value")
                            oracle_ts = payload.get("timestamp")

                            # Диагностика сырого сообщения (можно потом понизить до debug/info)
                            log.debug("[CHAINLINK RAW]",
                                        symbol=sym,
                                        value=val,
                                        oracle_ts=oracle_ts,
                                        ts_type=type(oracle_ts).__name__)

                            if val is None:
                                log.warning("[CHAINLINK SKIP] Missing value", symbol=sym)
                                continue

                            matched = False
                            for a, cs in CHAINLINK_SYMBOLS.items():
                                if sym == cs:
                                    matched = True
                                    try:
                                        ots = int(float(oracle_ts)) if oracle_ts is not None else None
                                        prices.update_chainlink(a, float(val), ots)
                                        log.debug("[CHAINLINK UPDATED]",
                                                    asset=a,
                                                    price=f"{float(val):.8f}",
                                                    oracle_ts_ms=ots,
                                                    chainlink_age=f"{prices.get_chainlink_age(a):.2f}s")
                                    except Exception as e:
                                        log.error("[CHAINLINK UPDATE FAILED]",
                                                  asset=a,
                                                  symbol=sym,
                                                  value=val,
                                                  oracle_ts=oracle_ts,
                                                  error=repr(e))
                                    break

                            if not matched:
                                log.debug("[CHAINLINK UNKNOWN SYMBOL]", symbol=sym)
                            continue

                        # ─────────────────────────────────────────────
                        # BINANCE FEED THROUGH RTDS
                        # ─────────────────────────────────────────────
                        elif topic == "crypto_prices":
                            sym = (payload.get("symbol") or "").lower()
                            val = payload.get("value")

                            if val is None:
                                continue

                            for a, bs in BINANCE_SYMBOLS_WS.items():
                                if sym == bs:
                                    try:
                                        prices.update_binance(a, float(val))
                                    except Exception as e:
                                        log.error("[BINANCE RTDS UPDATE FAILED]",
                                                  asset=a,
                                                  symbol=sym,
                                                  value=val,
                                                  error=repr(e))
                                    break

                    except json.JSONDecodeError as e:
                        log.error("[WS-RTDS] JSON decode error", error=repr(e), raw=raw[:300])
                        continue
                    except Exception as e:
                        log.error("[WS-RTDS] Message handling error", error=repr(e), raw=raw[:300])
                        continue

        except (websockets.exceptions.ConnectionClosed, ConnectionError, OSError) as e:
            log.warning("[WS-RTDS] Disconnected, reconnecting...", error=repr(e))
            await asyncio.sleep(WS_RECONNECT_DELAY)
        except Exception as e:
            log.error("[WS-RTDS] Fatal error", error=repr(e))
            await asyncio.sleep(WS_RECONNECT_DELAY)


_market_ws = None
_market_ws_lock = None


async def run_market_websocket():
    global _market_ws
    while True:
        try:
            async with websockets.connect(WS_MARKET_URL, ping_interval=WS_HEARTBEAT_INTERVAL) as ws:
                _market_ws = ws
                log.info("[WS-MARKET] Connected")
                async for raw in ws:
                    if raw == "PONG":
                        continue
                    try:
                        msg = json.loads(raw)
                        if isinstance(msg, list):
                            for item in msg:
                                if isinstance(item, dict):
                                    _process_market_msg(item)
                        elif isinstance(msg, dict):
                            _process_market_msg(msg)
                    except Exception:
                        continue
        except (websockets.exceptions.ConnectionClosed, ConnectionError, OSError):
            _market_ws = None
            log.warning("[WS-MARKET] Disconnected, reconnecting...")
            await asyncio.sleep(WS_RECONNECT_DELAY)
        except Exception as e:
            _market_ws = None
            log.error("[WS-MARKET] Error", error=str(e))
            await asyncio.sleep(WS_RECONNECT_DELAY)


def _process_market_msg(msg: dict):
    log.debug(f"RAW MSG: {msg}")
    et = msg.get("event_type", "")
    if et == "book":
        aid = msg.get("asset_id", "")
        bids = msg.get("bids", [])
        asks = msg.get("asks", [])
        if aid and isinstance(bids, list) and isinstance(asks, list):
            norm_bids = [{"price": b.get("price", "0"), "size": b.get("size", "0")} for b in bids if isinstance(b, dict)]
            norm_asks = [{"price": a.get("price", "0"), "size": a.get("size", "0")} for a in asks if isinstance(a, dict)]
            prices.update_full_book(aid, norm_bids, norm_asks)
    elif et == "price_change":
        aid = msg.get("asset_id", "")
        if aid:
            ba = msg.get("best_ask")
            bb = msg.get("best_bid")
            if ba or bb:
                try:
                    prices.update_lot_price(aid, float(ba) if ba else None, float(bb) if bb else None)
                except (ValueError, TypeError):
                    pass
        for pc in msg.get("price_changes", []):
            if isinstance(pc, dict):
                a = pc.get("asset_id", "")
                ba = pc.get("best_ask")
                bb = pc.get("best_bid")
                if a:
                    try:
                        prices.update_lot_price(a, float(ba) if ba else None, float(bb) if bb else None)
                    except (ValueError, TypeError):
                        pass
    elif et == "best_bid_ask":
        aid = msg.get("asset_id", "")
        ba = msg.get("best_ask")
        bb = msg.get("best_bid")
        if aid:
            try:
                prices.update_lot_price(aid, float(ba) if ba else None, float(bb) if bb else None)
            except (ValueError, TypeError):
                pass
    elif et == "last_trade_price":
        aid = msg.get("asset_id", "")
        p = msg.get("price")
        if aid and p:
            try:
                prices.update_lot_price(aid, float(p))
            except (ValueError, TypeError):
                pass


async def subscribe_market_tokens(token_ids):
    global _market_ws, _market_ws_lock
    if _market_ws is None:
        return
    if _market_ws_lock is None:
        _market_ws_lock = asyncio.Lock()
    try:
        async with _market_ws_lock:
            await _market_ws.send(json.dumps({
                "assets_ids": token_ids,
                "type": "market",
                "custom_feature_enabled": True
            }))
            log.info("[WS-MARKET] Subscribed", tokens=len(token_ids))
    except Exception as e:
        log.warning("[WS-MARKET] Subscribe failed", error=str(e))


def _normalize_api_creds(creds) -> Optional[Dict[str, str]]:
    if creds is None:
        return None
    if isinstance(creds, dict):
        api_key = creds.get("apiKey") or creds.get("key") or creds.get("api_key")
        secret = creds.get("secret") or creds.get("apiSecret") or creds.get("api_secret")
        passphrase = creds.get("passphrase") or creds.get("apiPassphrase") or creds.get("api_passphrase")
    else:
        api_key = getattr(creds, "apiKey", None) or getattr(creds, "key", None) or getattr(creds, "api_key", None)
        secret = getattr(creds, "secret", None) or getattr(creds, "apiSecret", None) or getattr(creds, "api_secret", None)
        passphrase = getattr(creds, "passphrase", None) or getattr(creds, "apiPassphrase", None) or getattr(creds, "api_passphrase", None)
    if api_key and secret and passphrase:
        return {"apiKey": api_key, "secret": secret, "passphrase": passphrase}
    return None


async def run_user_websocket():
    global _api_creds
    while True:
        if not _api_creds:
            await asyncio.sleep(1.0)
            continue
        try:
            async with websockets.connect(WS_USER_URL, ping_interval=WS_HEARTBEAT_INTERVAL) as ws:
                await ws.send(json.dumps({"type": "user", "auth": _api_creds}))
                log.info("[WS-USER] Connected")
                async for raw in ws:
                    if raw == "PONG":
                        continue
                    try:
                        msg = json.loads(raw)
                        if isinstance(msg, list):
                            for item in msg:
                                if isinstance(item, dict):
                                    _process_user_msg(item)
                        elif isinstance(msg, dict):
                            _process_user_msg(msg)
                    except Exception:
                        continue
        except (websockets.exceptions.ConnectionClosed, ConnectionError, OSError):
            log.warning("[WS-USER] Disconnected, reconnecting...")
            await asyncio.sleep(WS_RECONNECT_DELAY)
        except Exception as e:
            log.error("[WS-USER] Error", error=str(e))
            await asyncio.sleep(WS_RECONNECT_DELAY)


def _process_user_msg(msg: dict):
    event_type = (msg.get("event_type") or "").lower()
    if event_type == "order":
        oid = msg.get("id") or msg.get("order_id")
        if not oid:
            return
        try:
            fills.record_order_event(
                order_id=oid,
                side=(msg.get("side") or ""),
                limit_price=float(msg.get("price") or 0),
                original_size=float(msg.get("original_size") or msg.get("size") or 0),
                size_matched=float(msg.get("size_matched") or 0),
                status=(msg.get("status") or msg.get("type") or "")
            )
        except (ValueError, TypeError):
            pass
    elif event_type == "trade":
        taker_id = msg.get("taker_order_id") or msg.get("order_id")
        price = msg.get("price")
        size = msg.get("size")
        side = msg.get("side") or ""
        try:
            if taker_id and price and size:
                fills.record_trade_event(taker_id, side, float(price), float(size))
        except (ValueError, TypeError):
            pass
        for mo in msg.get("maker_orders", []) or []:
            if not isinstance(mo, dict):
                continue
            try:
                oid = mo.get("id") or mo.get("order_id") or mo.get("maker_order_id")
                pr = mo.get("price") or price
                sz = mo.get("size") or mo.get("matched_size") or size
                sd = mo.get("side") or side
                if oid and pr and sz:
                    fills.record_trade_event(oid, sd, float(pr), float(sz))
            except (ValueError, TypeError):
                continue


async def wait_for_fill(order_id: str, expected_size: int, timeout: float, fallback_price: float,
                        client=None, positions=None, stats=None) -> Dict[str, Any]:
    """
    v5.7.2.2: Now accepts optional client/positions/stats for concurrent SL monitoring.
    If provided, checks SL conditions every 50ms while waiting for fill.
    """
    deadline = time.time() + timeout
    while time.time() < deadline:
        # [PRIORITY] Check SL on other positions while waiting for fill
        if client is not None and positions is not None and stats is not None:
            await _check_sl_inline(client, positions, stats)
        
        snap = fills.snapshot(order_id)
        if snap:
            matched = max(float(snap.get("filled_size", 0)), float(snap.get("size_matched", 0)))
            if matched > 0:
                afp = snap.get("avg_fill_price", 0)
                avg_fill = afp if afp > 0 else (snap.get("limit_price", 0) or fallback_price)
                return {
                    "filled": True,
                    "matched_size": int(matched),
                    "avg_fill_price": float(avg_fill),
                    "actual_value": round(float(avg_fill) * float(matched), 4),
                    "status": snap.get("status"),
                }
        await asyncio.sleep(FILL_WAIT_INTERVAL)
    snap = fills.snapshot(order_id)
    if snap:
        matched = max(float(snap.get("filled_size", 0)), float(snap.get("size_matched", 0)))
        if matched > 0:
            afp = snap.get("avg_fill_price", 0)
            avg_fill = afp if afp > 0 else (snap.get("limit_price", 0) or fallback_price)
            return {
                "filled": True,
                "matched_size": int(matched),
                "avg_fill_price": float(avg_fill),
                "actual_value": round(float(avg_fill) * float(matched), 4),
                "status": snap.get("status"),
                "timed_out": True,
            }
    return {"filled": False, "matched_size": 0, "avg_fill_price": fallback_price, "actual_value": 0.0, "status": None}


async def _check_sl_inline(client, positions, stats):
    """
    v5.7.2.2: Lightweight SL check called every 50ms during wait_for_fill.
    Only triggers cascade SL, doesn't block.
    """
    now = time.time()
    for pos in list(positions.values()):
        if pos.closed or pos.sl_in_progress:
            continue
        if now >= pos.end_ts or now - pos.entry_timestamp < MONITOR_GRACE_PERIOD:
            continue
        cp = prices.get_lot_price(pos.token_id)
        if cp is None:
            continue
        
        # Determine SL trigger
        if pos.entry_type == EntryType.EARLY_TREND:
            if pos.partial_tp_taken:
                if cp <= pos.trailing_stop_price:
                    pos.sl_in_progress = True
                    asyncio.create_task(_run_cascade_sl_background(
                        client, pos, pos.trailing_stop_price, cp, stats))
                    log.warning(f"[{pos.asset}] SL during wait_for_fill (trailing)",
                                price=f"${cp:.4f}")
                continue
            sl = pos.entry_price * (1 - EARLY_TREND_SL_PCT)
        elif pos.entry_type == EntryType.VACUUM_SCALP:
            sl = pos.entry_price * (1 - VACUUM_SCALP_SL_PCT)
        else:
            sl = pos.entry_price * (1 - STANDARD_SL_PCT)
        
        if cp <= sl:
            pos.sl_in_progress = True
            asyncio.create_task(_run_cascade_sl_background(client, pos, sl, cp, stats))
            log.warning(f"[{pos.asset}] SL during wait_for_fill", price=f"${cp:.4f}", trigger=f"${sl:.4f}")


# ═══════════════════════════════════════════════════════════════════════════
# LOGGING
# ═══════════════════════════════════════════════════════════════════════════

class JSONFmt(logging.Formatter):
    def format(self, r):
        o = {"ts": datetime.fromtimestamp(r.created, tz=timezone.utc).isoformat(), "level": r.levelname, "msg": r.getMessage()}
        if hasattr(r, "extra") and isinstance(r.extra, dict):
            o.update(r.extra)
        return json.dumps(o, ensure_ascii=False, default=str)


class HumanFmt(logging.Formatter):
    C = {"DEBUG": "\033[36m", "INFO": "\033[32m", "WARNING": "\033[33m", "ERROR": "\033[31m", "CRITICAL": "\033[35m"}
    R = "\033[0m"

    def format(self, r):
        c = self.C.get(r.levelname, "")
        ts = self.formatTime(r, "%H:%M:%S")
        m = f"{ts} {c}[{r.levelname:7}]{self.R} {r.getMessage()}"
        if hasattr(r, "extra") and r.extra:
            m += f" {c}({' | '.join(f'{k}={v}' for k, v in r.extra.items())}){self.R}"
        return m


class SLog:
    def __init__(self, name, jf=None):
        self.l = logging.getLogger(name)
        self.l.setLevel(logging.INFO)
        self.l.handlers.clear()
        try:
            out = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace", line_buffering=True)
        except AttributeError:
            out = sys.stdout
        ch = logging.StreamHandler(out)
        ch.setFormatter(HumanFmt())
        self.l.addHandler(ch)
        if jf:
            d = os.path.dirname(jf)
            if d:
                os.makedirs(d, exist_ok=True)
            fh = RotatingFileHandler(jf, maxBytes=10 * 1024 * 1024, backupCount=5)
            fh.setFormatter(JSONFmt())
            self.l.addHandler(fh)

    def _log(self, lv, m, **k):
        self.l.log(lv, m, extra={"extra": k} if k else {})

    def info(self, m, **k):
        self._log(logging.INFO, m, **k)

    def warning(self, m, **k):
        self._log(logging.WARNING, m, **k)

    def error(self, m, **k):
        self._log(logging.ERROR, m, **k)

    def debug(self, m, **k):
        self._log(logging.DEBUG, m, **k)


log = SLog("polybot", jf="logs/polybot.json")


# ═══════════════════════════════════════════════════════════════════════════
# HTTP + UTILITIES
# ═══════════════════════════════════════════════════════════════════════════

def create_sync_session():
    s = requests.Session()
    r = urllib3.Retry(total=HTTP_RETRIES, backoff_factor=1, status_forcelist=[429, 500, 502, 503, 504], allowed_methods=["GET", "POST"])
    a = HTTPAdapter(max_retries=r, pool_connections=10, pool_maxsize=10)
    s.mount("https://", a)
    s.mount("http://", a)
    return s


_sync_http = create_sync_session()


class AsyncHTTP:
    def __init__(self):
        self._session = None

    async def session(self):
        if self._session is None or self._session.closed:
            self._session = aiohttp.ClientSession(
                connector=aiohttp.TCPConnector(limit=20, limit_per_host=10, keepalive_timeout=30)
            )
        return self._session

    async def get(self, url, params=None):
        try:
            sess = await self.session()
            async with sess.get(url, params=params, timeout=aiohttp.ClientTimeout(total=15, connect=5)) as r:
                r.raise_for_status()
                return await r.json()
        except (aiohttp.ClientError, asyncio.TimeoutError, RuntimeError):
            return None

    async def close(self):
        if self._session and not self._session.closed:
            await self._session.close()
            await asyncio.sleep(0.25)


_async_http = None


async def get_http():
    global _async_http
    if _async_http is None:
        _async_http = AsyncHTTP()
    return _async_http

async def get_interval_start_price_binance(asset: str, interval_ts: int) -> Optional[float]:
    """
    Получает open price 1-минутной свечи Binance на момент начала интервала.
    Это официальный способ — так делают все известные боты.
    """
    symbol = {"BTC": "BTCUSDT", "ETH": "ETHUSDT"}.get(asset)
    if not symbol:
        return None
    
    try:
        http = await get_http()
        # startTime в миллисекундах
        params = {
            "symbol": symbol,
            "interval": "1m",
            "startTime": interval_ts * 1000,
            "limit": 1
        }
        data = await http.get(f"{BINANCE_API}/klines", params)
        
        if data and len(data) > 0:
            # Kline format: [open_time, open, high, low, close, volume, ...]
            open_price = float(data[0][1])
            log.info(f"[{asset}] Binance start price", interval=interval_ts, price=f"${open_price:.2f}")
            return open_price
    except Exception as e:
        log.warning(f"[{asset}] Failed to get Binance start price", error=str(e))
    
    return None

def get_interval_start_price_chainlink(asset: str, interval_ts: int, max_drift_ms: int = 5000) -> Optional[float]:
    """
    Находит первую цену Chainlink с oracle_timestamp >= boundary.
    Это и есть Price to Beat, по которому резолвит Polymarket.
    """
    history = prices.chainlink_history.get(asset)
    if not history:
        return None
    
    boundary_ms = interval_ts * 1000
    best_price = None
    best_ts = None
    
    for oracle_ts_ms, _, price in history:
        # Ищем первую цену НА или ПОСЛЕ boundary
        if oracle_ts_ms >= boundary_ms:
            if best_ts is None or oracle_ts_ms < best_ts:
                best_ts = oracle_ts_ms
                best_price = price
    
    # Проверяем, что не слишком далеко от boundary
    if best_ts is not None and (best_ts - boundary_ms) <= max_drift_ms:
        return best_price
    
    # Fallback: ближайшая цена ДО boundary (но не старше 5 секунд)
    for oracle_ts_ms, _, price in reversed(list(history)):
        if oracle_ts_ms < boundary_ms and (boundary_ms - oracle_ts_ms) <= max_drift_ms:
            return price
    
    return None

async def get_or_set_interval_start_price(
    asset: str,
    interval_ts: int,
    allow_fallback: bool = True
) -> Optional[float]:
    """
    Приоритет источников:
    1. Chainlink boundary price (совпадает с Price to Beat)
    2. Binance open price (fallback, только если allow_fallback=True)
    3. Current oracle price (last resort, только если allow_fallback=True)
    """
    key = str(interval_ts)

    # Если уже есть в кеше — возвращаем
    if key in _interval_start_prices and asset in _interval_start_prices[key]:
        return _interval_start_prices[key][asset]

    if key not in _interval_start_prices:
        _interval_start_prices[key] = {}

    # 1) Основной источник — Chainlink boundary price
    price = get_interval_start_price_chainlink(asset, interval_ts)
    if price is not None:
        _interval_start_prices[key][asset] = price
        log.info(f"[{asset}] Start price from Chainlink",
                 interval=interval_ts, price=f"${price:.2f}")
        return price

    # Если fallback пока запрещён — просто выходим, НЕ кэшируя ничего
    if not allow_fallback:
        return None

    # 2) Binance fallback
    price = await get_interval_start_price_binance(asset, interval_ts)
    if price is not None:
        _interval_start_prices[key][asset] = price
        log.warning(f"[{asset}] Start price from Binance fallback",
                    interval=interval_ts, price=f"${price:.2f}")
        return price

    # 3) Последний fallback — текущий oracle price
    price = prices.get_oracle_price(asset)
    if price is not None:
        _interval_start_prices[key][asset] = price
        log.warning(f"[{asset}] Using current oracle as start price (last resort)",
                    price=f"${price:.2f}")
        return price

    return None

async def test_connection():
    endpoints = [
        ("CLOB", f"{CLOB_API}/time"),
        ("Gamma", f"{GAMMA_API}/markets?limit=1"),
        ("Binance", f"{BINANCE_API}/ticker/price?symbol=BTCUSDT")
    ]
    all_ok = True
    for name, url in endpoints:
        try:
            r = await asyncio.get_running_loop().run_in_executor(
                None, fp(_sync_http.get, url, timeout=HTTP_TIMEOUT))
            if r.status_code == 403:
                log.error(f"[NET] {name}: GEOBLOCK", status=403)
                all_ok = False
            elif r.status_code >= 400:
                log.warning(f"[NET] {name}: HTTP {r.status_code}", url=url)
                all_ok = False
            else:
                log.info(f"[NET] {name}: OK", status=r.status_code)
        except Exception as e:
            log.error(f"[NET] {name}: FAIL", error=str(e))
            if name != "Binance":
                all_ok = False
    return all_ok


def current_interval_ts(m=INTERVAL_MINUTES):
    n = int(time.time())
    return n - (n % (m * 60))


def next_interval_ts(m=INTERVAL_MINUTES):
    return current_interval_ts(m) + m * 60


async def run_sync(fn, *args):
    return await asyncio.get_running_loop().run_in_executor(None, fp(fn, *args))


def round_to_tick(price, ts="0.01"):
    try:
        t = Decimal(str(ts)) if ts else Decimal("0.01")
        if t <= 0:
            t = Decimal("0.01")
        p = Decimal(str(price))
        if p <= 0:
            return 0.001
        r = (p / t).to_integral_value(rounding=ROUND_FLOOR) * t
        return float(max(Decimal("0.001"), min(r, Decimal("0.999"))))
    except (InvalidOperation, ValueError, TypeError):
        return 0.001


def round_size(size):
    if size is None:
        return 0
    try:
        v = Decimal(str(size))
        return max(0, int(v.to_integral_value(rounding=ROUND_FLOOR))) if v >= 0 else 0
    except (InvalidOperation, ValueError, TypeError):
        return 0


def calc_base_stake(bal):
    if not bal or bal <= 0:
        return 0.0
    return float((Decimal(str(bal)) / 2).quantize(Decimal("0.01"), rounding=ROUND_DOWN))


def calc_stake_with_imbalance(bal, imb=0.5):
    base = calc_base_stake(bal)
    if not IMBALANCE_ENABLED or imb < MODERATE_IMBALANCE_THRESHOLD:
        return base
    mult = 1.0
    for th, m in sorted(IMBALANCE_STAKE_MULTIPLIERS.items(), reverse=True):
        if imb >= th:
            mult = m
            break
    return min(base * mult, bal * MAX_STAKE_RATIO)


def calc_early_trend_stake(bal):
    if not bal or bal <= 0:
        return 0.0
    return float(Decimal(str(bal * EARLY_TREND_MAX_STAKE_RATIO)).quantize(Decimal("0.01"), rounding=ROUND_DOWN))


def calc_vacuum_scalp_stake(bal, imb=0.5):
    if not bal or bal <= 0:
        return 0.0
    base = float(Decimal(str(bal * VACUUM_SCALP_MAX_STAKE_RATIO)).quantize(Decimal("0.01"), rounding=ROUND_DOWN))
    if not IMBALANCE_ENABLED or imb < MODERATE_IMBALANCE_THRESHOLD:
        return base
    mult = 1.0
    for th, m in sorted(IMBALANCE_STAKE_MULTIPLIERS.items(), reverse=True):
        if imb >= th:
            mult = m
            break
    return min(base * mult, bal * MAX_STAKE_RATIO)


def get_imbalance_confidence_boost(imb):
    if not IMBALANCE_ENABLED:
        return 0.0
    for th, b in sorted(IMBALANCE_CONFIDENCE_BOOST.items(), reverse=True):
        if imb >= th:
            return b
    return 0.0


_mpc = {}
_mpt = {}


def get_market_params(token_id):
    now = time.time()
    c = _mpc.get(token_id)
    if c and now - _mpt.get(token_id, 0) < 300:
        return c
    ts, nr = "0.01", False
    try:
        r = _sync_http.get(f"{CLOB_API}/tick-size", params={"token_id": token_id}, timeout=HTTP_TIMEOUT)
        if r.status_code == 200:
            d = r.json()
            ts = str(d.get("minimum_tick_size") or d.get("tick_size") or "0.01")
    except Exception:
        pass
    try:
        r = _sync_http.get(f"{CLOB_API}/neg-risk", params={"token_id": token_id}, timeout=HTTP_TIMEOUT)
        if r.status_code == 200:
            nr = r.json().get("neg_risk", False)
    except Exception:
        pass
    res = (ts, nr)
    _mpc[token_id] = res
    _mpt[token_id] = now
    return res


def extract_order_id(resp):
    if resp is None:
        return None
    if isinstance(resp, dict):
        return resp.get("orderID") or resp.get("order_id") or resp.get("id")
    for a in ["orderID", "order_id", "id"]:
        if hasattr(resp, a):
            return getattr(resp, a)
    return None


def fetch_wallet_usdc(client):
    try:
        r = client.get_balance_allowance(params=BalanceAllowanceParams(asset_type=AssetType.COLLATERAL))
        raw = r.get("balance", 0) or 0
        return round(int(raw) / 1_000_000, 4), True
    except Exception as e:
        log.warning(f"[WALLET] {e}")
        return 0.0, False


def get_real_balance(client):
    usdc, ok = fetch_wallet_usdc(client)
    if not ok:
        return None
    return round(usdc * BALANCE_SAFETY_MARGIN, 4)


def get_available_balance(client, positions):
    has_active_sl = any(pos.sl_in_progress for pos in positions.values())
    if not has_active_sl:
        try:
            client.cancel_all()
            log.debug("[BALANCE] Cleared orphaned orders")
        except Exception:
            pass
    total = get_real_balance(client)
    return total


def refresh_balance_for_early_entry(client, bs):
    wu, ok = fetch_wallet_usdc(client)
    if not ok:
        return {"updated": False, "bot_balance": bs.prev_bot_snap}
    if bs.prev_wallet_usdc is None:
        bs.prev_wallet_usdc = wu
        bs.prev_bot_snap = INITIAL_BALANCE
        return {"updated": True, "bot_balance": INITIAL_BALANCE}
    pa = round(wu - bs.prev_wallet_usdc, 4)
    nb = round(bs.prev_bot_snap + pa, 4)
    bs.prev_wallet_usdc = wu
    bs.prev_bot_snap = nb
    bs.total_profit += pa
    return {"updated": True, "bot_balance": nb}


def process_interval_snapshot(client, bs, interval_num, is_first):
    wu, ok = fetch_wallet_usdc(client)
    if not ok:
        return {"success": False, "bot_snap": bs.prev_bot_snap}
    if is_first:
        log.info(f"INITIAL SNAPSHOT #{interval_num}", wallet=f"${wu:.4f}")
        bs.prev_wallet_usdc = wu
        bs.prev_bot_snap = INITIAL_BALANCE
        return {"success": True, "bot_snap": INITIAL_BALANCE}
    pa = round(wu - bs.prev_wallet_usdc, 4)
    nb = round(bs.prev_bot_snap + pa, 4)
    log.info(f"SNAPSHOT #{interval_num}", usdc=f"${bs.prev_wallet_usdc:.4f} -> ${wu:.4f}", bot=f"${nb:.2f}")
    bs.prev_wallet_usdc = wu
    bs.prev_bot_snap = nb
    bs.total_profit += pa
    return {"success": True, "bot_snap": nb}


# ═══════════════════════════════════════════════════════════════════════════
# TREND TRACKING
# ═══════════════════════════════════════════════════════════════════════════

_trend_state: Dict[str, Dict] = {}


def track_oracle_price(slug, asset, op, tp):
    if slug not in _trend_state:
        _trend_state[slug] = {"asset": asset, "target": tp, "always_above": True, "always_below": True}
    rec = _trend_state[slug]
    if op is None or tp is None:
        return rec
    if op < tp:
        rec["always_above"] = False
    if op > tp:
        rec["always_below"] = False
    return rec


def analyze_trend(slug, asset):
    rec = _trend_state.get(slug)
    if not rec:
        return {"direction": None, "is_consistent": False, "current_deviation": 0}
    target = rec["target"]
    op = prices.get_oracle_price(asset)
    if op is None or target is None or target == 0:
        return {"direction": None, "is_consistent": False, "current_deviation": 0}
    dev = (op - target) / target
    if rec["always_above"]:
        d, ic = "UP", True
    elif rec["always_below"]:
        d, ic = "DOWN", True
    else:
        d = "UP" if dev > 0 else "DOWN"
        ic = False
    return {"direction": d, "is_consistent": ic, "current_deviation": dev, "oracle_price": op, "chainlink_age": prices.get_chainlink_age(asset)}


def check_micro_trend_ws(asset, direction):
    data = prices.get_micro_trend_data(asset, EARLY_TREND_MICRO_WINDOW)
    if len(data) < EARLY_TREND_MICRO_MIN_POINTS:
        return {"confirmed": False, "reason": "insufficient_data", "points": len(data)}
    rp = [p for _, p in data]
    avg = sum(rp) / len(rp)
    last = rp[-1]
    pct = (last - avg) / avg if avg > 0 else 0.0
    if direction == "UP":
        confirmed = pct > EARLY_TREND_MICRO_MIN_CHANGE_PCT
    elif direction == "DOWN":
        confirmed = pct < -EARLY_TREND_MICRO_MIN_CHANGE_PCT
    else:
        confirmed = False
    return {"confirmed": confirmed, "reason": "confirmed" if confirmed else "wrong_direction", "price_change_pct": pct, "points": len(rp)}


# ═══════════════════════════════════════════════════════════════════════════
# ANALYZE MARKET
# ═══════════════════════════════════════════════════════════════════════════

def _calc_series_stats(p):
    n = len(p)
    if n == 0:
        return None
    cur = p[-1]
    mn = min(p)
    avg = sum(p) / n
    trend = cur - avg
    mom = trend / avg if avg > 0 else 0.0
    cv = 0.0
    dc = 0
    if n >= MIN_PRICE_POINTS:
        vs = sum((x - avg) ** 2 for x in p)
        for i in range(2, n):
            if (p[i - 1] - p[i - 2]) * (p[i] - p[i - 1]) < 0:
                dc += 1
        cv = (vs / n) ** 0.5 / avg if avg > 0 else 0.0
    choppy = n >= MIN_PRICE_POINTS and (cv > MAX_CV or dc >= MAX_DIRECTION_CHANGES)
    return {"current": cur, "min": mn, "avg": avg, "trend": trend, "momentum": mom, "is_choppy": choppy}


def analyze_market(ph, slug, ws=PRICE_HIST_WINDOW):
    now = time.time()
    cutoff = now - ws
    up_p = [p for ts, p in ph.get(f"{slug}_UP", []) if ts >= cutoff]
    dn_p = [p for ts, p in ph.get(f"{slug}_DOWN", []) if ts >= cutoff]
    up = _calc_series_stats(up_p)
    dn = _calc_series_stats(dn_p)
    result = {
        "up_trend": 0.0, "down_trend": 0.0, "up_current": None, "down_current": None,
        "recommended": "NONE", "confidence": 0.0, "reason": "No data", "high_price_entry": False,
        "up_is_choppy": False, "down_is_choppy": False, "both_choppy": False
    }
    if up:
        result["up_current"] = up["current"]
        result["up_trend"] = up["trend"]
        result["up_is_choppy"] = up["is_choppy"]
    if dn:
        result["down_current"] = dn["current"]
        result["down_trend"] = dn["trend"]
        result["down_is_choppy"] = dn["is_choppy"]
    result["both_choppy"] = result["up_is_choppy"] and result["down_is_choppy"]
    if up is None and dn is None:
        return result
    if up is None or dn is None:
        s = up or dn
        d = "UP" if up else "DOWN"
        ic = result["up_is_choppy"] if up else result["down_is_choppy"]
        if ic:
            result["reason"] = f"Only {d} (chop)"
        elif s["trend"] > MIN_TREND_DIFF:
            result["recommended"] = d
            result["confidence"] = 0.5
            result["reason"] = f"Only {d}^"
        elif s["min"] >= HIGH_PRICE_THRESHOLD:
            result["recommended"] = d
            result["confidence"] = 0.5
            result["high_price_entry"] = True
        return result
    td = abs(up["trend"] - dn["trend"])
    md = up["momentum"] - dn["momentum"]
    uc, dc = result["up_is_choppy"], result["down_is_choppy"]

    def sr(d, c, r, fb=False):
        if fb:
            c *= FALLBACK_CONFIDENCE_MULTIPLIER
        result["recommended"] = d
        result["confidence"] = c
        result["reason"] = r

    def try_high_price():
        uo = up["min"] >= HIGH_PRICE_THRESHOLD and not uc
        do = dn["min"] >= HIGH_PRICE_THRESHOLD and not dc
        if uo and do:
            w = "UP" if up["min"] >= dn["min"] else "DOWN"
            sr(w, 0.5, f"{w} high")
            result["high_price_entry"] = True
        elif uo:
            sr("UP", 0.5, "UP high")
            result["high_price_entry"] = True
        elif do:
            sr("DOWN", 0.5, "DOWN high")
            result["high_price_entry"] = True

    if up["trend"] > 0 and dn["trend"] <= 0:
        if not uc:
            sr("UP", min(1.0, td / 0.02), "UP^ DOWNv")
    elif dn["trend"] > 0 and up["trend"] <= 0:
        if not dc:
            sr("DOWN", min(1.0, td / 0.02), "DOWN^ UPv")
    elif up["trend"] > 0 and dn["trend"] > 0:
        if md > MIN_TREND_DIFF and not uc:
            sr("UP", min(1.0, abs(md) / 0.02), "Both^, UP faster")
        elif md < -MIN_TREND_DIFF and not dc:
            sr("DOWN", min(1.0, abs(md) / 0.02), "Both^, DOWN faster")
        else:
            try_high_price()
    else:
        if up["trend"] > dn["trend"] + MIN_TREND_DIFF:
            if not uc:
                sr("UP", min(1.0, td / 0.02), "Bothv, UP slower")
        elif dn["trend"] > up["trend"] + MIN_TREND_DIFF:
            if not dc:
                sr("DOWN", min(1.0, td / 0.02), "Bothv, DOWN slower")
        else:
            try_high_price()
    return result


# ═══════════════════════════════════════════════════════════════════════════
# ORDER EXECUTION
# ═══════════════════════════════════════════════════════════════════════════

async def execute_buy_order_async(client, token_id, price, size, asset, tick_size=None, neg_risk=None,
                                   fill_timeout=BUY_FILL_TIMEOUT_EARLY, max_budget=None,
                                   positions=None, stats=None):
    """
    v5.7.2.2: Added positions/stats params for concurrent SL monitoring during wait_for_fill.
    """
    try:
        if max_budget is not None:
            avail = max_budget
        else:
            avail = await run_sync(get_real_balance, client)
        if avail is not None:
            needed = round(size * price, 4)
            if needed > avail:
                size = round_size(avail / price)
                if size < MIN_ORDER_SIZE:
                    log.warning(f"[{asset}] BUY rejected: insufficient available balance",
                                needed=f"${needed:.2f}", available=f"${avail:.2f}")
                    return {"success": False}
        if tick_size is None:
            tick_size, neg_risk = await run_sync(get_market_params, token_id)
        opts = PartialCreateOrderOptions(tick_size=tick_size, neg_risk=neg_risk)
        op = round_to_tick(price, tick_size)
        fn = fp(client.create_and_post_order,
                order_args=OrderArgs(token_id=token_id, price=op, size=size, side=Side.BUY),
                options=opts, order_type=OrderType.GTC)
        resp = await run_sync(fn)
        oid = extract_order_id(resp)
        log.info(f"[{asset}] BUY placed", price=op, size=size, order_id=oid)
        if not oid:
            return {"success": False, "error": "no_order_id"}

        # v5.7.2.2: Pass monitoring context to wait_for_fill for concurrent SL checks
        fill = await wait_for_fill(oid, size, fill_timeout, op,
                                   client=client, positions=positions, stats=stats)
        if not fill["filled"] or fill["matched_size"] < MIN_ORDER_SIZE:
            try:
                await run_sync(client.cancel, oid)
            except Exception:
                pass
            log.warning(f"[{asset}] BUY not filled in time", order_id=oid)
            return {"success": False, "error": "not_filled"}

        actual_price = round(fill["avg_fill_price"], 4)
        actual_size = int(fill["matched_size"])
        actual_cost = round(fill["actual_value"], 4)
        if actual_size < size:
            try:
                await run_sync(client.cancel, oid)
            except Exception:
                pass
            log.warning(f"[{asset}] BUY partial fill", filled=actual_size, requested=size, price=actual_price)

        log.info(f"[{asset}] BUY filled", price=actual_price, size=actual_size, cost=actual_cost, order_id=oid)
        return {"success": True, "order_id": oid, "price": actual_price, "size": actual_size, "cost": actual_cost}
    except Exception as e:
        log.error(f"[{asset}] BUY failed", error=str(e))
        return {"success": False, "error": str(e)}


async def execute_sell_order_async(client, token_id, size, asset, entry_price=0.0):
    try:
        tick_size, neg_risk = await run_sync(get_market_params, token_id)
        opts = PartialCreateOrderOptions(tick_size=tick_size, neg_risk=neg_risk)
        lp = prices.get_lot_price(token_id)
        sell_price = lp if lp and lp > 0 else entry_price
        if sell_price <= 0:
            return {"success": False, "error": "No price available"}

        fak_price = round_to_tick(sell_price - float(tick_size) * 2, tick_size)
        fak_price = max(round_to_tick(0.01, tick_size), fak_price)
        try:
            sell_order_type = OrderType.FAK if HAS_FAK else OrderType.FOK
            fn = fp(client.create_and_post_order,
                    order_args=OrderArgs(token_id=token_id, price=fak_price, size=size, side=Side.SELL),
                    options=opts, order_type=sell_order_type)
            resp = await run_sync(fn)
            oid = extract_order_id(resp)
            if oid:
                fill = await wait_for_fill(oid, size, 1.5, fak_price)
                if fill["filled"]:
                    matched = fill["matched_size"]
                    filled_proceeds = fill["actual_value"]
                    order_type_name = "FAK" if HAS_FAK else "FOK"
                    if matched >= size:
                        log.info(f"[{asset}] SELL {order_type_name} filled", size=matched,
                                 price=fill["avg_fill_price"], proceeds=filled_proceeds)
                        return {"success": True, "proceeds": filled_proceeds, "type": order_type_name}
                    remainder = size - matched
                    log.warning(f"[{asset}] SELL {order_type_name} partial", filled=matched, remainder=remainder,
                                price=fill["avg_fill_price"])
                    cp = lp if lp and lp > 0 else (entry_price * 0.95 if entry_price > 0 else None)
                    if cp and remainder >= MIN_ORDER_SIZE:
                        limit = round_to_tick(cp - float(tick_size) * 5, tick_size)
                        limit = max(round_to_tick(0.01, tick_size), limit)
                        fn = fp(client.create_and_post_order,
                                order_args=OrderArgs(token_id=token_id, price=limit, size=remainder, side=Side.SELL),
                                options=opts, order_type=OrderType.GTC)
                        resp = await run_sync(fn)
                        rem_oid = extract_order_id(resp)
                        log.info(f"[{asset}] SELL GTC remainder", price=limit, size=remainder, order_id=rem_oid)
                        return {"success": True, "proceeds": filled_proceeds, "type": "FAK+GTC", "pending": True}
                    return {"success": True, "proceeds": filled_proceeds, "type": order_type_name}
        except Exception as e:
            log.debug(f"[{asset}] FAK/FOK failed: {e}")

        cp = lp if lp and lp > 0 else (entry_price * 0.95 if entry_price > 0 else None)
        if not cp:
            return {"success": False, "error": "No price for GTC"}
        limit = round_to_tick(cp - float(tick_size) * 5, tick_size)
        limit = max(round_to_tick(0.01, tick_size), limit)
        fn = fp(client.create_and_post_order,
                order_args=OrderArgs(token_id=token_id, price=limit, size=size, side=Side.SELL),
                options=opts, order_type=OrderType.GTC)
        resp = await run_sync(fn)
        oid = extract_order_id(resp)
        proceeds = round(size * limit, 4)
        log.info(f"[{asset}] SELL GTC", price=limit, size=size, order_id=oid)
        return {"success": True, "proceeds": proceeds, "type": "GTC", "pending": True}
    except Exception as e:
        log.error(f"[{asset}] SELL failed", error=str(e))
        return {"success": False, "error": str(e)}


async def place_gtc_sell_order(client, token_id, size, price, asset):
    try:
        tick_size, neg_risk = await run_sync(get_market_params, token_id)
        opts = PartialCreateOrderOptions(tick_size=tick_size, neg_risk=neg_risk)
        sell_price = round_to_tick(price, tick_size)
        fn = fp(client.create_and_post_order,
                order_args=OrderArgs(token_id=token_id, price=sell_price, size=size, side=Side.SELL),
                options=opts, order_type=OrderType.GTC)
        resp = await run_sync(fn)
        oid = extract_order_id(resp)
        if oid:
            log.info(f"[{asset}] VACUUM TP order placed", price=sell_price, size=size, order_id=oid)
            return {"success": True, "order_id": oid, "price": sell_price}
        return {"success": False, "error": "no_order_id"}
    except Exception as e:
        log.error(f"[{asset}] VACUUM TP order failed", error=str(e))
        return {"success": False, "error": str(e)}


# ═══════════════════════════════════════════════════════════════════════════
# CASCADING SL
# ═══════════════════════════════════════════════════════════════════════════

async def execute_cascading_sl_sell(client, token_id, size, asset, entry_price, current_price, sl_trigger):
    tick_size, neg_risk = await run_sync(get_market_params, token_id)
    opts = PartialCreateOrderOptions(tick_size=tick_size, neg_risk=neg_risk)
    nuclear_threshold = sl_trigger * (1 - NUCLEAR_CRASH_PCT)
    remaining = size
    total_proceeds = 0.0

    if current_price <= nuclear_threshold:
        log.error(f"[{asset}] NUCLEAR EXIT: crash detected",
                  price=f"${current_price:.4f}", threshold=f"${nuclear_threshold:.4f}")
        fn = fp(client.create_and_post_order,
                order_args=OrderArgs(token_id=token_id, price=NUCLEAR_SELL_PRICE, size=remaining, side=Side.SELL),
                options=opts, order_type=OrderType.GTC)
        try:
            await run_sync(fn)
        except Exception as e:
            log.error(f"[{asset}] NUCLEAR EXIT failed", error=str(e))
        proceeds = round(remaining * current_price * 0.5, 4)
        return {"success": True, "proceeds": proceeds, "exit_type": "NUCLEAR_CRASH"}

    lp = prices.get_lot_price(token_id)
    sell_price = lp if lp and lp > 0 else current_price
    slippage_price = round_to_tick(sell_price * (1 - SL_DYNAMIC_SLIPPAGE_PCT), tick_size)
    slippage_price = max(round_to_tick(0.01, tick_size), slippage_price)

    sell_order_type = OrderType.FAK if HAS_FAK else OrderType.FOK
    try:
        fn = fp(client.create_and_post_order,
                order_args=OrderArgs(token_id=token_id, price=slippage_price, size=remaining, side=Side.SELL),
                options=opts, order_type=sell_order_type)
        resp = await run_sync(fn)
        oid = extract_order_id(resp)
        if oid:
            fill = await wait_for_fill(oid, remaining, 1.5, slippage_price)
            if fill["filled"]:
                matched = fill["matched_size"]
                filled_proceeds = fill["actual_value"]
                if matched >= remaining:
                    total_proceeds += filled_proceeds
                    log.info(f"[{asset}] SL FAK filled", size=matched, proceeds=total_proceeds)
                    return {"success": True, "proceeds": total_proceeds, "exit_type": "FAK"}
                total_proceeds += filled_proceeds
                remaining -= matched
                log.info(f"[{asset}] SL FAK partial", filled=matched, remaining=remaining)
    except Exception as e:
        log.debug(f"[{asset}] SL FAK failed: {e}")

    chase_price = slippage_price
    last_oid = None

    for chase_round in range(SL_MAX_CHASE_ROUNDS):
        if remaining < MIN_ORDER_SIZE:
            break

        fresh_price = prices.get_lot_price(token_id)
        if fresh_price and fresh_price <= nuclear_threshold:
            log.error(f"[{asset}] NUCLEAR during chase round {chase_round + 1}",
                      price=f"${fresh_price:.4f}")
            fn = fp(client.create_and_post_order,
                    order_args=OrderArgs(token_id=token_id, price=NUCLEAR_SELL_PRICE, size=remaining, side=Side.SELL),
                    options=opts, order_type=OrderType.GTC)
            try:
                await run_sync(fn)
            except Exception:
                pass
            total_proceeds += round(remaining * (fresh_price or 0.01) * 0.5, 4)
            return {"success": True, "proceeds": total_proceeds, "exit_type": f"NUCLEAR_CHASE_R{chase_round + 1}"}

        chase_price = round_to_tick(chase_price * (1 - SL_CHASE_STEP_PCT), tick_size)
        chase_price = max(round_to_tick(0.01, tick_size), chase_price)

        try:
            fn = fp(client.create_and_post_order,
                    order_args=OrderArgs(token_id=token_id, price=chase_price, size=remaining, side=Side.SELL),
                    options=opts, order_type=OrderType.GTC)
            resp = await run_sync(fn)
            last_oid = extract_order_id(resp)
            log.info(f"[{asset}] SL CHASE R{chase_round + 1}", price=chase_price, size=remaining, order_id=last_oid)
        except Exception as e:
            log.warning(f"[{asset}] SL CHASE R{chase_round + 1} place failed", error=str(e))
            continue

        if last_oid:
            fill = await wait_for_fill(last_oid, remaining, SL_CHASE_TIMEOUT, chase_price)
            if fill["filled"]:
                matched = fill["matched_size"]
                total_proceeds += fill["actual_value"]
                remaining -= matched
                if remaining < MIN_ORDER_SIZE:
                    log.info(f"[{asset}] SL CHASE R{chase_round + 1} filled", proceeds=total_proceeds)
                    return {"success": True, "proceeds": total_proceeds, "exit_type": f"CHASE_R{chase_round + 1}"}
                try:
                    await run_sync(client.cancel, last_oid)
                except Exception:
                    pass
            else:
                try:
                    await run_sync(client.cancel, last_oid)
                except Exception:
                    pass

    if remaining >= MIN_ORDER_SIZE:
        log.error(f"[{asset}] NUCLEAR OPTION: chase exhausted", remaining=remaining)
        try:
            fn = fp(client.create_and_post_order,
                    order_args=OrderArgs(token_id=token_id, price=NUCLEAR_SELL_PRICE, size=remaining, side=Side.SELL),
                    options=opts, order_type=OrderType.GTC)
            await run_sync(fn)
        except Exception as e:
            log.error(f"[{asset}] NUCLEAR OPTION failed", error=str(e))
        fresh = prices.get_lot_price(token_id) or 0.01
        total_proceeds += round(remaining * fresh * 0.5, 4)

    return {"success": True, "proceeds": total_proceeds, "exit_type": "NUCLEAR_FINAL"}


# ═══════════════════════════════════════════════════════════════════════════
# EARLY EXIT
# ═══════════════════════════════════════════════════════════════════════════

def check_early_exit_opportunity_ws(pos):
    if not EARLY_EXIT_ENABLED:
        return {"can_exit": False}
    if pos.entry_type == EntryType.EARLY_TREND and pos.trailing_active:
        return {"can_exit": False}
    if pos.entry_type == EntryType.VACUUM_SCALP:
        return {"can_exit": False}
    stc = pos.end_ts - time.time()
    if stc > EARLY_EXIT_WINDOW or stc <= 0:
        return {"can_exit": False}
    if pos.entry_price <= 0 or pos.current_size <= 0:
        return {"can_exit": False}
    if pos.entry_price >= EARLY_EXIT_SKIP_ABOVE_PRICE:
        return {"can_exit": False}
    book = prices.get_book(pos.token_id)
    if book is None:
        return {"can_exit": False}
    bv = book.get("bid_volume", 0)
    av = book.get("ask_volume", 0)
    t = bv + av
    imb = bv / t if t > 0 else 0.5
    is_vacuum = (av == 0 and bv > 0) or (imb >= VACUUM_IMBALANCE_THRESHOLD and bv > 0)
    if not is_vacuum:
        return {"can_exit": False}
    bb = book.get("best_bid")
    if bb is None or bb <= 0:
        return {"can_exit": False}
    profit_per_lot = bb - pos.entry_price
    if profit_per_lot < EARLY_EXIT_MIN_PROFIT:
        return {"can_exit": False}
    return {"can_exit": True, "best_bid": bb}


# ═══════════════════════════════════════════════════════════════════════════
# EARLY TREND ENTRY
# ═══════════════════════════════════════════════════════════════════════════

def check_early_trend_opportunity_ws(market, asset, traded):
    if not EARLY_TREND_ENABLED:
        return {"can_enter": False}
    slug = market["slug"]
    if slug in traded:
        return {"can_enter": False}
    stc = market["end_ts"] - time.time()
    if stc <= 0 or stc <= EARLY_TREND_CUTOFF_SECS:
        return {"can_enter": False}
    tp = market.get("target_price")
    if tp is None:
        return {"can_enter": False}
    op = prices.get_oracle_price(asset)
    if op is None:
        return {"can_enter": False}
    track_oracle_price(slug, asset, op, tp)
    trend = analyze_trend(slug, asset)
    if not trend["is_consistent"]:
        return {"can_enter": False}
    if abs(trend["current_deviation"]) < EARLY_TREND_MIN_DEVIATION:
        return {"can_enter": False}
    direction = trend["direction"]
    token_id = market["up_token_id"] if direction == "UP" else market["down_token_id"]
    if not token_id:
        return {"can_enter": False}
    book = prices.get_book(token_id)
    if book is None:
        return {"can_enter": False}
    ba = book.get("best_ask")
    if ba is None:
        return {"can_enter": False}
    spread = book.get("spread")
    if not (EARLY_TREND_MIN_PRICE <= ba <= EARLY_TREND_MAX_PRICE):
        return {"can_enter": False}
    if spread is not None and spread > EARLY_TREND_MAX_SPREAD:
        return {"can_enter": False}
    micro = check_micro_trend_ws(asset, direction)
    if not micro["confirmed"]:
        return {"can_enter": False}
    return {
        "can_enter": True, "direction": direction, "token_id": token_id, "entry_price": ba,
        "target_price": tp, "oracle_price": op, "deviation": trend["current_deviation"],
        "secs_to_close": stc, "micro_trend_pct": micro["price_change_pct"],
        "chainlink_age": trend.get("chainlink_age", 0)
    }


async def execute_early_trend_entry_async(client, asset, ei, bot_balance, positions=None, stats=None):
    token_id = ei["token_id"]
    direction = ei["direction"]
    ep = ei["entry_price"]
    stake = calc_early_trend_stake(bot_balance)
    if stake <= 0:
        return {"success": False}
    tick_size, neg_risk = await run_sync(get_market_params, token_id)
    op = round_to_tick(ep, tick_size)
    ts = round_size(stake / op)
    if ts < MIN_ORDER_SIZE:
        return {"success": False}
    oc = round(ts * op, 4)
    while oc > stake and ts >= MIN_ORDER_SIZE:
        ts -= 1
        oc = round(ts * op, 4)
    if ts < MIN_ORDER_SIZE:
        return {"success": False}
    avail = await run_sync(get_available_balance, client, positions or {})
    log.info(f"[{asset}] EARLY TREND {direction}", price=op, size=ts, cost=oc,
             deviation=f"{ei['deviation'] * 100:+.2f}%", oracle=f"${ei['oracle_price']:.2f}")
    # [PRIORITY] Pre-entry SL guard: check other positions before buying
    if await check_and_handle_urgent_sl(client, positions, stats):
        log.warning(f"[{asset}] EARLY TREND aborted: urgent SL on another position")
        return {"success": False, "reason": "urgent_sl_elsewhere"}
    result = await execute_buy_order_async(client, token_id, op, ts, asset, tick_size, neg_risk,
                                           max_budget=avail, positions=positions, stats=stats)
    if result["success"]:
        ap = result["price"]
        return {
            "success": True, "order_id": result["order_id"], "price": ap, "size": result["size"],
            "cost": result["cost"], "direction": direction,
            "limit_price": op,
            "take_profit_price": round(ap * (1 + EARLY_TREND_TP_PCT), 4),
            "stop_loss_price": round(ap * (1 - EARLY_TREND_SL_PCT), 4)
        }
    return {"success": False}


def _parse_market_data(raw, slug):
    """
    Парсит данные маркета из Gamma API.
    target_price берётся из кеша стартовых цен (заполняется асинхронно).
    """
    if not isinstance(raw, dict):
        return None

    ids = json.loads(raw.get("clobTokenIds", "[]"))
    
    # Определяем актив по slug
    asset = None
    slug_lower = slug.lower()
    question_lower = (raw.get("question") or "").lower()
    
    for a in ASSETS:
        if a.lower() in slug_lower:
            asset = a
            break
    
    # Fallback по ключевым словам в question
    if asset is None:
        if "bitcoin" in question_lower or "btc" in question_lower:
            asset = "BTC"
        elif "ethereum" in question_lower or "eth" in question_lower:
            asset = "ETH"
    
    # target_price = start price интервала (из кеша, если есть)
    interval_ts = current_interval_ts()
    key = str(interval_ts)
    target = None
    
    if key in _interval_start_prices and asset in _interval_start_prices[key]:
        target = _interval_start_prices[key][asset]
    
    # Если target ещё нет — он будет установлен асинхронно в main loop
    
    return {
        "slug": slug,
        "asset": asset,
        "up_token_id": ids[0] if ids else None,
        "down_token_id": ids[1] if len(ids) > 1 else None,
        "end_ts": next_interval_ts(),
        "target_price": target
    }


async def fetch_market_async(asset):
    slug = f"{asset.lower()}-updown-{INTERVAL_MINUTES}m-{current_interval_ts()}"
    cached = _gamma_cache.get(slug)
    if cached:
        result, ts = cached
        if time.time() - ts < GAMMA_CACHE_TTL:
            # Обновляем target_price из кеша start prices (может появиться позже)
            if result and result.get("target_price") is None:
                key = str(current_interval_ts())
                if key in _interval_start_prices and asset in _interval_start_prices[key]:
                    result["target_price"] = _interval_start_prices[key][asset]
            return result
    
    http = await get_http()
    data = await http.get(f"{GAMMA_API}/markets", {"slug": slug, "active": "true", "closed": "false", "limit": "5"})
    if not data or not isinstance(data, list) or len(data) == 0:
        _gamma_cache[slug] = (None, time.time())
        return None
    
    result = _parse_market_data(data[0], slug)
    
    # Убедимся, что asset установлен
    if result:
        result["asset"] = asset
        
        # Попробуем получить target_price из кеша
        if result.get("target_price") is None:
            key = str(current_interval_ts())
            if key in _interval_start_prices and asset in _interval_start_prices[key]:
                result["target_price"] = _interval_start_prices[key][asset]
    
    _gamma_cache[slug] = (result, time.time())
    return result


# ═══════════════════════════════════════════════════════════════════════════
# VACUUM SCALP STRATEGY (FIXED)
# ═══════════════════════════════════════════════════════════════════════════

def check_vacuum_scalp_opportunity(market, asset, traded, bot_balance) -> Dict[str, Any]:
    if not VACUUM_SCALP_ENABLED:
        return {"can_enter": False, "reason": "disabled"}
    
    slug = market["slug"]
    if slug in traded:
        return {"can_enter": False, "reason": "already_traded"}
    
    interval_duration = INTERVAL_MINUTES * 60
    stc = market["end_ts"] - time.time()
    time_since_start = interval_duration - stc
    
    if time_since_start < VACUUM_SCALP_ENTRY_START_SECS:
        return {"can_enter": False, "reason": f"too_early ({time_since_start:.0f}s < {VACUUM_SCALP_ENTRY_START_SECS}s)"}
    if stc < VACUUM_SCALP_ENTRY_END_SECS:
        return {"can_enter": False, "reason": f"too_late ({stc:.0f}s < {VACUUM_SCALP_ENTRY_END_SECS}s)"}
    
    # ════════════════════════════════════════════════
    # СБОР ДАННЫХ (один раз)
    # ════════════════════════════════════════════════
    tp = market.get("target_price")
    op = prices.get_oracle_price(asset)
    deviation = (op - tp) / tp if (tp and op and tp > 0) else None
    
    direction = "UP" if (deviation and deviation > 0) else "DOWN"
    token_id = market["up_token_id"] if direction == "UP" else market["down_token_id"]
    
    book = prices.get_book_with_max_age(token_id, VACUUM_SCALP_BOOK_MAX_AGE) if token_id else None
    token_price = book.get("best_ask") if book else None
    bid_volume = book.get("bid_volume", 0) if book else 0
    book_age = (time.time() - book["ts"]) if (book and book.get("ts")) else None
    volatility = prices.get_volatility(asset, VACUUM_SCALP_VOLATILITY_WINDOW)
    
    imb = prices.get_book_imbalance(token_id) if token_id else 0.5
    potential_stake = calc_vacuum_scalp_stake(bot_balance, imb)
    potential_size = round_size(potential_stake / token_price) if token_price else 0
    potential_value = potential_size * token_price if token_price else 0
    required_liquidity = potential_size * VACUUM_SCALP_LIQUIDITY_RATIO

    # ════════════════════════════════════════════════
    # ДИАГНОСТИКА (до проверок)
    # ════════════════════════════════════════════════
    now = time.time()
    if now - _vacuum_diag_last_log.get(asset, 0) >= 5.0:
        _vacuum_diag_last_log[asset] = now
        log.debug(f"[{asset}] VACUUM DIAG",
                 stc=f"{stc:.0f}s",
                 deviation=f"{deviation*100:+.4f}%" if deviation else "N/A",
                 token_price=f"${token_price:.2f}" if token_price else "N/A",
                 volatility=f"{volatility*100:.4f}%" if volatility else "N/A",
                 bid_vol=f"{bid_volume:.0f}",
                 req_liq=f"{required_liquidity:.0f}",
                 book_age=f"{book_age:.1f}s" if book_age else "stale",
                 order_val=f"${potential_value:.2f}" if potential_value else "N/A",
        )

    # ════════════════════════════════════════════════
    # ПРОВЕРКИ (используют те же переменные)
    # ════════════════════════════════════════════════
    if tp is None or tp <= 0:
        return {"can_enter": False, "reason": "no_target_price"}
    
    if op is None:
        return {"can_enter": False, "reason": "no_oracle_price"}
    
    if abs(deviation) < VACUUM_SCALP_MIN_DEVIATION:
        return {"can_enter": False, "reason": f"deviation_too_small ({abs(deviation)*100:.3f}% < {VACUUM_SCALP_MIN_DEVIATION*100:.2f}%)"}

    if not token_id:
        return {"can_enter": False, "reason": "no_token_id"}

    if book is None:
        return {"can_enter": False, "reason": f"book_stale_or_missing (max_age={VACUUM_SCALP_BOOK_MAX_AGE}s)"}

    if token_price is None or token_price < VACUUM_SCALP_MIN_TOKEN_PRICE:
        return {"can_enter": False, "reason": f"token_price_too_low ({token_price or 0:.2f} < {VACUUM_SCALP_MIN_TOKEN_PRICE})"}
    
    if token_price > VACUUM_SCALP_MAX_TOKEN_PRICE:
        return {"can_enter": False, "reason": f"token_price_too_high ({token_price:.2f} > {VACUUM_SCALP_MAX_TOKEN_PRICE})"}
    
    # Кросс-валидация направления
    opposite_token_id = market["down_token_id"] if direction == "UP" else market["up_token_id"]
    if opposite_token_id:
        opposite_book = prices.get_book_with_max_age(opposite_token_id, VACUUM_SCALP_BOOK_MAX_AGE)
        if opposite_book:
            opposite_price = opposite_book.get("best_ask")
            if opposite_price is not None and opposite_price >= VACUUM_SCALP_MIN_TOKEN_PRICE:
                return {"can_enter": False, 
                        "reason": f"direction_conflict (both tokens expensive: "
                                  f"{direction}=${token_price:.2f}, "
                                  f"opposite=${opposite_price:.2f})"}
    
    # Стабильность deviation
    history = prices.binance_direct_history.get(asset) or prices.chainlink_history.get(asset)
    if history and tp > 0:
        recent_cutoff = time.time() - 10.0
        recent_prices = [p for ts, p in history if ts >= recent_cutoff]
        if len(recent_prices) >= 2:
            above_count = sum(1 for p in recent_prices if p > tp)
            below_count = sum(1 for p in recent_prices if p < tp)
            if above_count > 0 and below_count > 0:
                return {"can_enter": False, 
                        "reason": f"price_crossed_target (above={above_count}, "
                                  f"below={below_count} in last 10s)"}
    
    # Волатильность (используем уже вычисленную)
    if volatility is None:
        return {"can_enter": False, "reason": "insufficient_volatility_data"}
    if volatility > VACUUM_SCALP_MAX_VOLATILITY:
        return {"can_enter": False, "reason": f"volatility_too_high ({volatility*100:.3f}% > {VACUUM_SCALP_MAX_VOLATILITY*100:.2f}%)"}
    
    # Размер ордера (используем уже вычисленные)
    if potential_value < MIN_ORDER_VALUE:
        return {"can_enter": False, "reason": f"order_value_too_small (${potential_value:.2f} < ${MIN_ORDER_VALUE})"}
    
    if potential_size < MIN_ORDER_SIZE:
        return {"can_enter": False, "reason": "insufficient_balance"}
    
    # Ликвидность (используем уже вычисленную)
    if bid_volume < required_liquidity:
        return {"can_enter": False, "reason": f"insufficient_liquidity (bids={bid_volume:.0f} < {required_liquidity:.0f})"}

    # ════════════════════════════════════════════════
    # ВСЕ ПРОВЕРКИ ПРОЙДЕНЫ
    # ════════════════════════════════════════════════
    log.info(f"[{asset}] VACUUM ENTRY ALLOWED", direction=direction, price=f"${token_price:.2f}")
    
    return {
        "can_enter": True,
        "direction": direction,
        "token_id": token_id,
        "entry_price": token_price,
        "target_price": tp,
        "oracle_price": op,
        "deviation": deviation,
        "volatility": volatility,
        "bid_volume": bid_volume,
        "potential_size": potential_size,
        "imbalance": imb,
        "secs_to_close": stc
    }


async def execute_vacuum_scalp_entry_async(client, asset, ei, bot_balance, positions, stats):
    token_id = ei["token_id"]
    direction = ei["direction"]
    entry_price = ei["entry_price"]
    imb = ei.get("imbalance", 0.5)
    
    stake = calc_vacuum_scalp_stake(bot_balance, imb)
    if stake <= 0:
        return {"success": False}
    
    tick_size, neg_risk = await run_sync(get_market_params, token_id)
    buy_price = round_to_tick(entry_price, tick_size)
    order_size = round_size(stake / buy_price)
    
    if order_size < MIN_ORDER_SIZE:
        return {"success": False}
    
    order_cost = round(order_size * buy_price, 4)
    
    # ──── ПРОВЕРКА: минимальная стоимость ордера ────
    if order_cost < MIN_ORDER_VALUE:
        log.warning(f"[{asset}] VACUUM SCALP rejected: order value ${order_cost:.2f} < ${MIN_ORDER_VALUE}")
        return {"success": False, "reason": "order_value_too_small"}
    
    while order_cost > stake and order_size >= MIN_ORDER_SIZE:
        order_size -= 1
        order_cost = round(order_size * buy_price, 4)
    
    if order_size < MIN_ORDER_SIZE or order_cost < MIN_ORDER_VALUE:
        return {"success": False}
    
    avail = await run_sync(get_available_balance, client, positions)
    
    log.info(f"[{asset}] VACUUM SCALP {direction}",
             price=buy_price, size=order_size, cost=order_cost,
             deviation=f"{ei['deviation']*100:+.3f}%",
             volatility=f"{ei['volatility']*100:.3f}%",
             bid_support=f"{ei['bid_volume']:.0f}")
    
    # Pre-entry SL guard
    if await check_and_handle_urgent_sl(client, positions, stats):
        log.warning(f"[{asset}] VACUUM SCALP aborted: urgent SL on another position")
        return {"success": False, "reason": "urgent_sl_elsewhere"}
    
    result = await execute_buy_order_async(
        client, token_id, buy_price, order_size, asset,
        tick_size, neg_risk, fill_timeout=BUY_FILL_TIMEOUT_VACUUM, max_budget=avail,
        positions=positions, stats=stats
    )
    
    if not result.get("success"):
        return {"success": False}
    
    actual_price = result["price"]
    actual_size = result["size"]
    actual_cost = result["cost"]

    # ──── ПРОВЕРКА: аномальное исполнение ────
    if entry_price > 0 and actual_price < entry_price * (1 - FILL_ANOMALY_PCT):
        log.error(f"[{asset}] VACUUM ANOMALOUS FILL: ${actual_price:.4f} vs expected ${entry_price:.4f}")
        return {
            "success": True,
            "order_id": result["order_id"],
            "price": actual_price,
            "size": actual_size,
            "cost": actual_cost,
            "direction": direction,
            "anomalous": True,  # ← Флаг для nuclear exit
            "tp_price": 0,
            "tp_order_id": None,
            "tp_timestamp": 0.0,
            "stop_loss_price": 0,
            "tp_pending": False
        }
    
    if actual_price < 0.98:
        tp_price = round_to_tick(actual_price + VACUUM_SCALP_TP_DELTA, tick_size)
    else:
        tp_price = round_to_tick(actual_price + 0.01, tick_size)
    
    # ──── ИСПРАВЛЕНИЕ: задержка перед TP и retry ────
    # Ждём чтобы токены зачислились на баланс
    await asyncio.sleep(2.0)
    
    tp_order_id = None
    tp_timestamp = 0.0
    tp_retry_count = 0
    max_tp_retries = 3
    
    while tp_retry_count < max_tp_retries:
        tp_result = await place_gtc_sell_order(client, token_id, actual_size, tp_price, asset)
        
        if tp_result.get("success"):
            tp_order_id = tp_result.get("order_id")
            tp_timestamp = time.time()
            log.info(f"[{asset}] VACUUM TP set", entry=actual_price, tp=tp_price, order_id=tp_order_id)
            break
        else:
            tp_retry_count += 1
            error_msg = tp_result.get("error", "")
            log.warning(f"[{asset}] VACUUM TP retry {tp_retry_count}/{max_tp_retries}", error=error_msg)
            
            if tp_retry_count < max_tp_retries:
                await asyncio.sleep(0.5 * tp_retry_count)  # Увеличивающаяся задержка
    
    if tp_order_id is None:
        log.warning(f"[{asset}] VACUUM TP failed — starting background retry")
    
    return {
        "success": True,
        "order_id": result["order_id"],
        "price": actual_price,
        "size": actual_size,
        "cost": actual_cost,
        "direction": direction,
        "tp_price": tp_price,
        "tp_order_id": tp_order_id,
        "tp_timestamp": tp_timestamp,
        "stop_loss_price": round(actual_price * (1 - VACUUM_SCALP_SL_PCT), 4),
        "tp_pending": tp_order_id is None  # ← Флаг для приоритетного retry
    }


# ═══════════════════════════════════════════════════════════════════════════
# BACKGROUND SL TASKS
# ═══════════════════════════════════════════════════════════════════════════

async def _run_nuclear_exit_background(client, pos, stats):
    try:
        sz = pos.current_size
        tick_size, neg_risk = await run_sync(get_market_params, pos.token_id)
        opts = PartialCreateOrderOptions(tick_size=tick_size, neg_risk=neg_risk)
        fn = fp(client.create_and_post_order,
                order_args=OrderArgs(token_id=pos.token_id, price=NUCLEAR_SELL_PRICE, size=sz, side=Side.SELL),
                options=opts, order_type=OrderType.GTC)
        await run_sync(fn)
        lp = prices.get_lot_price(pos.token_id) or pos.entry_price * 0.5
        proceeds = round(sz * lp * 0.5, 4)
        pnl = proceeds - (sz * pos.entry_price)
        pos.record_close(CloseReason.STOP_LOSS, pnl, proceeds)
        stats.record(pnl, pos.entry_type, CloseReason.STOP_LOSS)
        log.error(f"[{pos.asset}] NUCLEAR EXIT COMPLETE", pnl=f"${pnl:.2f}")
    except Exception as e:
        log.error(f"[{pos.asset}] NUCLEAR EXIT FAILED", error=str(e))
        pos.sl_in_progress = False


async def _run_cascade_sl_background(client, pos, sl_trigger, current_price, stats):
    try:
        if pos.tp_order_id:
            try:
                await run_sync(client.cancel, pos.tp_order_id)
                log.info(f"[{pos.asset}] Cancelled TP order before SL", order_id=pos.tp_order_id)
            except Exception:
                pass
        
        sz = pos.current_size
        r = await execute_cascading_sl_sell(client, pos.token_id, sz, pos.asset, pos.entry_price, current_price, sl_trigger)
        if r["success"]:
            pnl = r["proceeds"] - (sz * pos.entry_price)
            pos.record_close(CloseReason.STOP_LOSS, pnl, r["proceeds"])
            stats.record(pnl, pos.entry_type, CloseReason.STOP_LOSS)
            log.warning(f"[{pos.asset}] SL [{r.get('exit_type', '?')}]",
                        price=f"${current_price:.4f}", trigger=f"${sl_trigger:.4f}", pnl=f"${pnl:.2f}")
        else:
            log.error(f"[{pos.asset}] SL FAILED", error=r.get("error", "unknown"))
            pos.sl_in_progress = False
    except Exception as e:
        log.error(f"[{pos.asset}] SL background task error", error=str(e))
        pos.sl_in_progress = False

async def _retry_tp_background(client, pos):
    """Фоновая задача для retry TP ордера. Не блокирует main loop."""
    max_retries = 5
    
    for attempt in range(1, max_retries + 1):
        if pos.closed or pos.sl_in_progress or pos.tp_order_placed:
            return  # Позиция закрыта или TP уже выставлен
        
        await asyncio.sleep(0.5 * attempt)  # Нарастающая задержка
        
        if pos.closed or pos.sl_in_progress:
            return
        
        tp_result = await place_gtc_sell_order(
            client, pos.token_id, pos.current_size, pos.take_profit_price, pos.asset
        )
        
        if tp_result.get("success"):
            pos.tp_order_id = tp_result.get("order_id")
            pos.tp_order_placed = True
            pos.tp_pending_priority = False
            pos.tp_order_timestamp = time.time()
            log.info(f"[{pos.asset}] VACUUM TP placed (background retry #{attempt})",
                     price=pos.take_profit_price, order_id=pos.tp_order_id)
            return
        else:
            log.warning(f"[{pos.asset}] VACUUM TP background retry #{attempt}/{max_retries}",
                        error=tp_result.get("error", ""))
    
    log.error(f"[{pos.asset}] VACUUM TP background retries exhausted — monitor will handle")
    pos.tp_pending_priority = False


# ═══════════════════════════════════════════════════════════════════════════
# v5.7.2.2: PRE-ENTRY SL GUARD — prevents buying while another position needs SL
# ═══════════════════════════════════════════════════════════════════════════

async def check_and_handle_urgent_sl(client, positions, stats) -> bool:
    """
    Lightweight SL-only check (~0.1ms) called before EVERY buy attempt.
    Returns True if any SL was triggered (caller should abort entry).
    
    This ensures SL monitoring is prioritised over new entries.
    During a buy (which blocks for 1-3s with wait_for_fill), other
    positions' SL conditions are still checked via this guard.
    """
    now = time.time()
    triggered = False
    for slug, pos in list(positions.items()):
        if pos.closed or pos.sl_in_progress:
            continue
        if now >= pos.end_ts or now - pos.entry_timestamp < MONITOR_GRACE_PERIOD:
            continue
        cp = prices.get_lot_price(pos.token_id)
        if cp is None:
            continue
        # Determine SL trigger based on entry type
        if pos.entry_type == EntryType.EARLY_TREND:
            if pos.partial_tp_taken:
                pos.update_trailing(cp)
                if cp <= pos.trailing_stop_price:
                    triggered = True
                    pos.sl_in_progress = True
                    asyncio.create_task(_run_cascade_sl_background(
                        client, pos, pos.trailing_stop_price, cp, stats))
                    log.warning(f"[{pos.asset}] URGENT: trailing stop breach before entry",
                                price=f"${cp:.4f}", trailing=f"${pos.trailing_stop_price:.4f}")
                continue
            sl = pos.entry_price * (1 - EARLY_TREND_SL_PCT)
        elif pos.entry_type == EntryType.VACUUM_SCALP:
            sl = pos.entry_price * (1 - VACUUM_SCALP_SL_PCT)
        else:
            sl = pos.entry_price * (1 - STANDARD_SL_PCT)
        if cp <= sl:
            triggered = True
            pos.sl_in_progress = True
            asyncio.create_task(_run_cascade_sl_background(client, pos, sl, cp, stats))
            log.warning(f"[{pos.asset}] URGENT: SL breach before entry",
                        price=f"${cp:.4f}", trigger=f"${sl:.4f}")
    return triggered


# ═══════════════════════════════════════════════════════════════════════════
# MONITORING (FIXED)
# ═══════════════════════════════════════════════════════════════════════════

async def monitor_positions_async(client, positions, bot_balance, stats):
    """
    v5.7.2.1: Fixed vacuum scalp monitoring:
    - [FIX] No double proceeds accounting
    - [FIX] TP timeout handling
    """
    now = time.time()
    bd = 0.0
    events = []
    active = [p for p in positions.values()
              if not p.closed and now < p.end_ts and now - p.entry_timestamp >= MONITOR_GRACE_PERIOD]
    if not active:
        return {"bot_balance": bot_balance, "balance_delta": 0.0, "events": []}

    for pos in active:
        cp = prices.get_lot_price(pos.token_id)
        if cp is None:
            continue

        # VACUUM SCALP MONITORING
        if pos.entry_type == EntryType.VACUUM_SCALP:
            if pos.sl_in_progress:
                continue
            
            # Check if TP order is filled
            if pos.tp_order_id and pos.tp_order_placed:
                if fills.is_filled(pos.tp_order_id):
                    snap = fills.snapshot(pos.tp_order_id)
                    if snap:
                        filled_size = max(snap.get("filled_size", 0), snap.get("size_matched", 0))
                        avg_price = snap.get("avg_fill_price", 0) or pos.take_profit_price
                        proceeds = round(filled_size * avg_price, 4)
                        pnl = proceeds - (filled_size * pos.entry_price)
                        pos.record_close(CloseReason.VACUUM_TP, pnl, proceeds)
                        # [FIX] Don't add proceeds to bd - already on exchange balance
                        stats.record(pnl, pos.entry_type, CloseReason.VACUUM_TP)
                        log.info(f"[{pos.asset}] VACUUM TP HIT",
                                 entry=f"${pos.entry_price:.4f}",
                                 tp=f"${avg_price:.4f}",
                                 pnl=f"+${pnl:.4f}")
                        continue
                
                # [FIX] Check for TP timeout - cancel stale TP and let it expire/SL
                if pos.tp_order_timestamp > 0:
                    tp_age = now - pos.tp_order_timestamp
                    if tp_age > VACUUM_SCALP_TP_TIMEOUT_SECS:
                        log.warning(f"[{pos.asset}] VACUUM TP timeout ({tp_age:.0f}s), cancelling")
                        try:
                            await run_sync(client.cancel, pos.tp_order_id)
                        except Exception:
                            pass
                        pos.tp_order_id = None
                        pos.tp_order_placed = False
            
            # If TP order not placed yet, try to place it
            if not pos.tp_order_placed and pos.take_profit_price > 0:
                tp_result = await place_gtc_sell_order(
                    client, pos.token_id, pos.current_size, pos.take_profit_price, pos.asset
                )
                if tp_result.get("success"):
                    pos.tp_order_id = tp_result.get("order_id")
                    pos.tp_order_placed = True
                    pos.tp_order_timestamp = time.time()
                    log.info(f"[{pos.asset}] VACUUM TP placed (retry)", 
                             price=pos.take_profit_price, order_id=pos.tp_order_id)
            
            # Check SL
            sl_trigger = pos.entry_price * (1 - VACUUM_SCALP_SL_PCT)
            if cp <= sl_trigger:
                pos.sl_in_progress = True
                asyncio.create_task(_run_cascade_sl_background(
                    client, pos, sl_trigger, cp, stats))
            continue

        # EARLY TREND MONITORING
        if pos.entry_type == EntryType.EARLY_TREND:
            pp = (cp - pos.entry_price) / pos.entry_price if pos.entry_price > 0 else 0
            if not pos.partial_tp_taken:
                if pp >= EARLY_TREND_TP_PCT:
                    cs = round_size(pos.current_size * EARLY_TREND_PARTIAL_TP_RATIO)
                    if cs >= MIN_ORDER_SIZE:
                        r = await execute_sell_order_async(client, pos.token_id, cs, pos.asset, pos.entry_price)
                        if r["success"]:
                            pnl = r["proceeds"] - (cs * pos.entry_price)
                            trail = max(cp * (1 - TRAILING_STOP_DISTANCE_PCT),
                                        pos.entry_price * (1 + TRAILING_STOP_MIN_PROFIT_PCT))
                            pos.record_partial_tp(cs, pnl, trail)
                            bd += r["proceeds"]
                            stats.record(pnl, pos.entry_type, CloseReason.PARTIAL_TP)
                            log.info(f"[{pos.asset}] PARTIAL TP", pnl=f"+${pnl:.2f}", trailing=f"${trail:.4f}")
                    continue
                if pp <= -EARLY_TREND_SL_PCT:
                    sz = pos.current_size
                    r = await execute_sell_order_async(client, pos.token_id, sz, pos.asset, pos.entry_price)
                    if r["success"]:
                        pnl = r["proceeds"] - (sz * pos.entry_price)
                        pos.record_close(CloseReason.STOP_LOSS, pnl, r["proceeds"])
                        bd += r["proceeds"]
                        stats.record(pnl, pos.entry_type, CloseReason.STOP_LOSS)
                        log.warning(f"[{pos.asset}] STOP LOSS", pnl=f"${pnl:.2f}")
                    continue
            else:
                pos.update_trailing(cp)
                if cp <= pos.trailing_stop_price:
                    sz = pos.current_size
                    r = await execute_sell_order_async(client, pos.token_id, sz, pos.asset, pos.entry_price)
                    if r["success"]:
                        pnl = r["proceeds"] - (sz * pos.entry_price)
                        pos.record_close(CloseReason.TRAILING_STOP, pnl, r["proceeds"])
                        bd += r["proceeds"]
                        stats.record(pos.total_pnl, pos.entry_type, CloseReason.TRAILING_STOP)
                        log.info(f"[{pos.asset}] TRAILING EXIT", pnl=f"${pnl:.2f}")
                    continue

        # STANDARD ENTRY MONITORING
        else:
            if pos.sl_in_progress:
                continue
            if EARLY_EXIT_ENABLED:
                ei = check_early_exit_opportunity_ws(pos)
                if ei.get("can_exit"):
                    r = await execute_sell_order_async(client, pos.token_id, pos.current_size, pos.asset, pos.entry_price)
                    if r["success"]:
                        profit = r["proceeds"] - (pos.current_size * pos.entry_price)
                        pos.record_close(CloseReason.EARLY_EXIT, profit, r["proceeds"])
                        bd += r["proceeds"]
                        stats.record(profit, pos.entry_type, CloseReason.EARLY_EXIT)
                        log.info(f"[{pos.asset}] EARLY EXIT", profit=f"${profit:+.2f}")
                    continue
            sl_trigger = pos.entry_price * (1 - STANDARD_SL_PCT)
            if cp <= sl_trigger:
                pos.sl_in_progress = True
                asyncio.create_task(_run_cascade_sl_background(
                    client, pos, sl_trigger, cp, stats))

    return {"bot_balance": bot_balance + bd, "balance_delta": bd, "events": events}


# ═══════════════════════════════════════════════════════════════════════════
# STANDARD ENTRY
# ═══════════════════════════════════════════════════════════════════════════

async def check_and_execute_standard_entry(client, asset, market, bot_balance, ph, traded, positions, stats):
    if not STANDARD_ENTRY_ENABLED:
        return bot_balance
    if bot_balance <= 0:
        return bot_balance
    slug = market["slug"]
    if slug in traded:
        return bot_balance
    up_id, dn_id = market["up_token_id"], market["down_token_id"]
    end_ts = market["end_ts"]
    stc = end_ts - time.time()
    up_p = prices.get_lot_price(up_id) if up_id else None
    dn_p = prices.get_lot_price(dn_id) if dn_id else None
    if up_p is None and dn_p is None:
        return bot_balance
    now_ts = time.time()
    for sfx, pr in [("_UP", up_p), ("_DOWN", dn_p)]:
        key = slug + sfx
        if key not in ph:
            ph[key] = deque(maxlen=DEQUE_MAXLEN)
        if pr is not None:
            ph[key].append((now_ts, pr))
    if not (0 < stc <= ENTRY_WINDOW_SECS):
        return bot_balance
    analysis = analyze_market(ph, slug)
    if analysis["both_choppy"]:
        return bot_balance
    rec = analysis["recommended"]
    conf = analysis["confidence"]
    if conf < MIN_CONFIDENCE:
        return bot_balance
    hpe = analysis["high_price_entry"]
    direction = token_id = current_price = None
    up_avail = up_p is not None and up_p >= MIN_LOT_PRICE
    dn_avail = dn_p is not None and dn_p >= MIN_LOT_PRICE
    if rec == "UP" and up_avail:
        direction, token_id, current_price = "UP", up_id, up_p
    elif rec == "DOWN" and dn_avail:
        direction, token_id, current_price = "DOWN", dn_id, dn_p
    if not direction or not current_price:
        return bot_balance
    imb_boost = get_imbalance_confidence_boost(prices.get_book_imbalance(token_id))
    conf = min(1.0, conf + imb_boost)
    if conf < MIN_CONFIDENCE:
        return bot_balance
    avail_bal = await run_sync(get_available_balance, client, positions)
    effective = min(bot_balance, avail_bal) if avail_bal is not None else bot_balance
    tick_size, neg_risk = await run_sync(get_market_params, token_id)

    imb = prices.get_book_imbalance(token_id)
    stake = calc_stake_with_imbalance(effective, imb)
    if stake <= 0:
        return bot_balance
    total_size = round_size(stake / current_price)
    if total_size < MIN_ORDER_SIZE:
        return bot_balance
    buy_price = round_to_tick(STANDARD_BUY_PRICE, tick_size)
    worst_cost = round(total_size * buy_price, 4)
    while worst_cost > effective and total_size >= MIN_ORDER_SIZE:
        total_size -= 1
        worst_cost = round(total_size * buy_price, 4)
    if total_size < MIN_ORDER_SIZE:
        return bot_balance

    et = EntryType.HIGH_PRICE if hpe else EntryType.STANDARD

    # При входе по High Price сначала проверяем, есть ли вообще ликвидность в стакане (заявки на продажу)
    if et == EntryType.HIGH_PRICE:
        book = prices.get_book(token_id)
        if not book or not book.get("asks"):
            log.warning(f"[{asset}] HIGH PRICE ENTRY aborted: no ask liquidity in orderbook")
            return bot_balance

    log.info(f"[{asset}] ENTRY {direction} [{et.value}] AGGRESSIVE",
             buy_price=buy_price, lots=total_size, conf=f"{conf:.0%}")

    # [PRIORITY] Pre-entry SL guard: check other positions before buying
    if await check_and_handle_urgent_sl(client, positions, stats):
        log.warning(f"[{asset}] STANDARD ENTRY aborted: urgent SL on another position")
        return bot_balance

    result = await execute_buy_order_async(client, token_id, buy_price, total_size, asset, tick_size, neg_risk,
                                           max_budget=effective, positions=positions, stats=stats)
    if result.get("success"):
        ap = result["price"]
        actual_size = result["size"]
        actual_cost = result["cost"]
        bot_balance = max(0.0, bot_balance - actual_cost)
        traded.add(slug)

        if current_price > 0 and ap < current_price * (1 - FILL_ANOMALY_PCT):
            log.error(f"[{asset}] ANOMALOUS FILL: ${ap:.4f} vs expected ${current_price:.4f}")
            log.error(f"[{asset}] IMMEDIATE NUCLEAR EXIT")
            positions[slug] = Position(
                slug=slug, asset=asset, token_id=token_id, direction=direction,
                entry_price=ap, entry_size=actual_size, entry_cost=actual_cost, entry_type=et,
                order_id=result["order_id"], end_ts=end_ts, real_cost=actual_cost,
                order_locked_cost=round(buy_price * actual_size, 4), confidence=conf
            )
            pos = positions[slug]
            pos.sl_in_progress = True
            asyncio.create_task(_run_nuclear_exit_background(client, pos, stats))
            return bot_balance

        positions[slug] = Position(
            slug=slug, asset=asset, token_id=token_id, direction=direction,
            entry_price=ap, entry_size=actual_size, entry_cost=actual_cost, entry_type=et,
            order_id=result["order_id"], end_ts=end_ts, real_cost=actual_cost,
            order_locked_cost=round(buy_price * actual_size, 4),
            confidence=conf, stop_loss_price=round(ap * (1 - STANDARD_SL_PCT), 4)
        )
        log.info(f"[{asset}] FILLED at ${ap:.4f} (bid ${buy_price})",
                 actual_cost=f"${actual_cost:.2f}", size=actual_size)
    return bot_balance


# ═══════════════════════════════════════════════════════════════════════════
# INIT + CLEANUP (FIXED)
# ═══════════════════════════════════════════════════════════════════════════

def init_client():
    global _api_creds
    c = ClobClient(CLOB_API, key=PRIVATE_KEY, chain_id=CHAIN_ID_POLYGON, signature_type=SIGNATURE_TYPE, funder=FUNDER_ADDRESS)
    creds = c.derive_api_key()
    c.set_api_creds(creds)
    _api_creds = _normalize_api_creds(creds)
    if _api_creds:
        log.info("User WS creds ready")
    else:
        log.warning("User WS creds unavailable; fill tracking may fall back to limit prices")
    log.info("Client initialized", funder=f"{FUNDER_ADDRESS[:10]}...{FUNDER_ADDRESS[-6:]}")
    return c


def graceful_shutdown(client, positions):
    for slug, pos in positions.items():
        if not pos.closed:
            if pos.tp_order_id:
                try:
                    client.cancel(pos.tp_order_id)
                    log.info("[SHUTDOWN] Cancelled TP order", asset=pos.asset)
                except:
                    pass
            if pos.order_id:
                try:
                    client.cancel(pos.order_id)
                    log.info("[SHUTDOWN] Cancelled", asset=pos.asset)
                except:
                    pass


def cleanup_old_data(cur_ts, positions, traded, stats):
    now = time.time()
    cutoff_fills = now - INTERVAL_MINUTES * 60 * 2
    fills.orders = {k: v for k, v in fills.orders.items() if v.get("last_ts", 0) > cutoff_fills}
    _gamma_cache.clear()
    
    # Очистка старых стартовых цен (старше 3 интервалов)
    for key in list(_interval_start_prices.keys()):
        try:
            if now - int(key) > INTERVAL_MINUTES * 60 * 3:
                _interval_start_prices.pop(key, None)
        except (ValueError, TypeError):
            _interval_start_prices.pop(key, None)
    
    for slug in list(_trend_state.keys()):
        try:
            parts = slug.rsplit("-", 1)
            if len(parts) == 2 and now - int(parts[-1]) > INTERVAL_MINUTES * 60 * 2:
                _trend_state.pop(slug, None)
        except Exception:
            pass
    
    for slug, pos in list(positions.items()):
        if not pos.closed and now >= pos.end_ts:
            if pos.tp_order_id:
                try:
                    pass  # Будет очищено cancel_all
                except Exception:
                    pass
            pnl = -pos.entry_cost
            pos.record_close(CloseReason.EXPIRED, pnl)
            stats.record(pnl, pos.entry_type, CloseReason.EXPIRED)
            log.warning(f"[{pos.asset}] EXPIRED", pnl=f"${pnl:.2f}")
        if pos.closed and now >= pos.end_ts + 60:
            positions.pop(slug, None)
    
    return {s for s in traded if str(cur_ts) in s}


# ═══════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════

async def main_async():
    log.info("=" * 60)
    log.info("POLYMARKET BOT v5.7.3 -- Binance start price + Direct WS")
    log.info("=" * 60)
    log.info(f"Assets: {ASSETS} | Balance: ${INITIAL_BALANCE:.2f}")
    active_strats = []
    if EARLY_TREND_ENABLED: active_strats.append("Early Trend")
    if VACUUM_SCALP_ENABLED: active_strats.append("Vacuum Scalp")
    if STANDARD_ENTRY_ENABLED: active_strats.append("Standard")
    log.info(f"Strategies: {', '.join(active_strats)}")
    log.info(f"Vacuum: TP +${VACUUM_SCALP_TP_DELTA} | SL -{VACUUM_SCALP_SL_PCT*100:.0f}% | Window {VACUUM_SCALP_ENTRY_START_SECS}-{INTERVAL_MINUTES*60-VACUUM_SCALP_ENTRY_END_SECS}s")
    log.info(f"Monitor: every {MONITOR_INTERVAL * 1000:.0f}ms | Loop: every {POLL_INTERVAL * 1000:.0f}ms")
    log.info("=" * 60)

    conn_ok = await test_connection()
    if not conn_ok:
        log.error("Essential APIs unreachable. Check VPN/proxy and internet.")
        return

    client = await run_sync(init_client)
    usdc, ok = await run_sync(fetch_wallet_usdc, client)
    if ok:
        log.info(f"Wallet USDC: ${usdc:.4f}")

    ws_rtds_task = asyncio.create_task(run_rtds_websocket())
    ws_market_task = asyncio.create_task(run_market_websocket())
    ws_user_task = asyncio.create_task(run_user_websocket())
    ws_binance_direct_task = asyncio.create_task(run_binance_direct_websocket())

    bot_balance = INITIAL_BALANCE
    bs = BalanceState()
    snapshot_done = False
    stats = TradeStats()
    ph: Dict[str, Deque] = {}
    traded: Set[str] = set()
    positions: Dict[str, Position] = {}
    last_interval = 0
    last_monitor = 0.0
    last_blog = 0.0
    known_tokens: Set[str] = set()

    try:
        log.info("Waiting for WebSocket data...")
        for _ in range(50):
            if prices.chainlink or prices.binance:
                break
            await asyncio.sleep(0.1)
        if prices.chainlink:
            log.info("Chainlink OK", assets=list(prices.chainlink.keys()))
        if prices.binance:
            log.info("Binance OK", assets=list(prices.binance.keys()))

        while True:
            t0 = time.time()
            cur = current_interval_ts()

            # Сколько прошло с начала текущего интервала
            secs_from_interval_start = time.time() - cur

            for asset in ASSETS:
                key = str(cur)
                already_cached = key in _interval_start_prices and asset in _interval_start_prices.get(key, {})

                if not already_cached:
                    # В первые START_PRICE_CHAINLINK_GRACE_SECS секунд
                    # ждём именно Chainlink и НЕ даём Binance fallback закэшироваться слишком рано
                    allow_fallback = secs_from_interval_start >= START_PRICE_CHAINLINK_GRACE_SECS

                    start_price = await get_or_set_interval_start_price(
                        asset,
                        cur,
                        allow_fallback=allow_fallback
                    )

                    if start_price is not None:
                        log.info(f"[{asset}] Start price set", interval=cur, price=f"${start_price:.2f}")
            
            ste = next_interval_ts() - int(t0)
            ac = sum(1 for p in positions.values() if not p.closed and time.time() < p.end_ts)

            if ac > 0 and (t0 - last_monitor) >= MONITOR_INTERVAL:
                mr = await monitor_positions_async(client, positions, bot_balance, stats)
                bot_balance = mr["bot_balance"]
                last_monitor = t0

            for pos in positions.values():
                if pos.closed and pos.sl_in_progress:
                    bot_balance += pos.close_proceeds
                    pos.sl_in_progress = False

            if 0 < ste <= SNAPSHOT_BEFORE_END and not snapshot_done:
                is_first = bs.prev_wallet_usdc is None
                r = await run_sync(process_interval_snapshot, client, bs, bs.intervals_passed + 1, is_first)
                if r["success"]:
                    bot_balance = r["bot_snap"]
                    if not is_first:
                        pct = (bs.total_profit / INITIAL_BALANCE * 100) if INITIAL_BALANCE > 0 else 0
                        log.info(f"[SNAPSHOT] Total: ${bs.total_profit:+.4f} ({pct:+.2f}%)")
                snapshot_done = True

            if last_interval != cur:
                if last_interval != 0:
                    bs.intervals_passed += 1
                    traded = cleanup_old_data(cur, positions, traded, stats)
                last_interval = cur
                snapshot_done = False

            markets = await asyncio.gather(*[fetch_market_async(a) for a in ASSETS])
            new_tokens = []
            for market in markets:
                if market:
                    for tid in [market.get("up_token_id"), market.get("down_token_id")]:
                        if tid and tid not in known_tokens:
                            new_tokens.append(tid)
                            known_tokens.add(tid)
            if new_tokens:
                log.debug(f"Subscribing to: {new_tokens}")
                await subscribe_market_tokens(new_tokens)

            for asset, market in zip(ASSETS, markets):
                if bot_balance <= 0 or not market:
                    continue
                slug = market["slug"]
                if slug in traded:
                    continue
                stc = market["end_ts"] - time.time()
                tp = market.get("target_price")
                op = prices.get_oracle_price(asset)
                if tp and op:
                    track_oracle_price(slug, asset, op, tp)

                            
                # STRATEGY 1: EARLY TREND (first priority, >120s to close)
                if EARLY_TREND_ENABLED and stc > EARLY_TREND_CUTOFF_SECS:
                    eo = check_early_trend_opportunity_ws(market, asset, traded)
                    if eo.get("can_enter"):
                        rr = await run_sync(refresh_balance_for_early_entry, client, bs)
                        if rr["updated"]:
                            bot_balance = rr["bot_balance"]
                        r = await execute_early_trend_entry_async(client, asset, eo, bot_balance, positions, stats)
                        if r.get("success"):
                            bot_balance = max(0.0, bot_balance - r["cost"])
                            traded.add(slug)
                            positions[slug] = Position(
                                slug=slug, asset=asset, token_id=eo["token_id"], direction=r["direction"],
                                entry_price=r["price"], entry_size=r["size"], entry_cost=r["cost"],
                                entry_type=EntryType.EARLY_TREND, order_id=r["order_id"], end_ts=market["end_ts"],
                                take_profit_price=r["take_profit_price"], stop_loss_price=r["stop_loss_price"],
                                real_cost=r["cost"],
                                order_locked_cost=round(r.get("limit_price", r["price"]) * r["size"], 4),
                                confidence=0.7, target_price=eo["target_price"],
                                entry_deviation=eo["deviation"]
                            )
                            continue

                # STRATEGY 2: VACUUM SCALP (120s-270s from start, i.e. 30-180s to close)
                if VACUUM_SCALP_ENABLED and stc > VACUUM_SCALP_ENTRY_END_SECS:
                    vo = check_vacuum_scalp_opportunity(market, asset, traded, bot_balance)
                    if vo.get("can_enter"):
                        r = await execute_vacuum_scalp_entry_async(client, asset, vo, bot_balance, positions, stats)
                        if r.get("success"):
                            bot_balance = max(0.0, bot_balance - r["cost"])
                            traded.add(slug)
                            
                            # ──── ANOMALOUS FILL → NUCLEAR EXIT ────
                            if r.get("anomalous"):
                                log.error(f"[{asset}] VACUUM IMMEDIATE NUCLEAR EXIT")
                                positions[slug] = Position(
                                    slug=slug, asset=asset, token_id=vo["token_id"], direction=r["direction"],
                                    entry_price=r["price"], entry_size=r["size"], entry_cost=r["cost"],
                                    entry_type=EntryType.VACUUM_SCALP, order_id=r["order_id"], end_ts=market["end_ts"],
                                    real_cost=r["cost"],
                                    order_locked_cost=round(r["price"] * r["size"], 4),
                                    confidence=0.9, target_price=vo["target_price"],
                                    entry_deviation=vo["deviation"]
                                )
                                pos = positions[slug]
                                pos.sl_in_progress = True
                                asyncio.create_task(_run_nuclear_exit_background(client, pos, stats))
                                continue
                            
                            # Нормальный вход
                            positions[slug] = Position(
                                slug=slug, asset=asset, token_id=vo["token_id"], direction=r["direction"],
                                entry_price=r["price"], entry_size=r["size"], entry_cost=r["cost"],
                                entry_type=EntryType.VACUUM_SCALP, order_id=r["order_id"], end_ts=market["end_ts"],
                                take_profit_price=r["tp_price"], stop_loss_price=r["stop_loss_price"],
                                real_cost=r["cost"],
                                order_locked_cost=round(r["price"] * r["size"], 4),
                                confidence=0.9, target_price=vo["target_price"],
                                entry_deviation=vo["deviation"],
                                tp_order_id=r.get("tp_order_id"),
                                tp_order_placed=r.get("tp_order_id") is not None,
                                tp_order_timestamp=r.get("tp_timestamp", 0.0),
                                tp_pending_priority=r.get("tp_pending", False)
                            )
                            
                            # Если TP не выставлен — фоновый retry
                            if r.get("tp_pending"):
                                asyncio.create_task(_retry_tp_background(client, positions[slug]))
                        
                            continue

                # STRATEGY 3: STANDARD ENTRY (last 11s)
                if STANDARD_ENTRY_ENABLED and 0 < stc <= ENTRY_WINDOW_SECS:
                    bot_balance = await check_and_execute_standard_entry(
                        client, asset, market, bot_balance, ph, traded, positions, stats
                    )

            if QUIET_MODE and (t0 - last_blog) >= BALANCE_LOG_INTERVAL:
                cl_age = prices.get_chainlink_age("BTC")
                log.info(f"Balance: ${bot_balance:.2f} | Pos: {ac}", chainlink_age=f"{cl_age:.0f}s")
                last_blog = t0

            elapsed = time.time() - t0
            if elapsed > 0.5:
                log.warning(f"CRITICAL LAG: Loop took {elapsed:.2f}s")
            await asyncio.sleep(max(0.0, POLL_INTERVAL - elapsed))

    except (KeyboardInterrupt, asyncio.CancelledError):
        log.info("\n" + "=" * 60)
        log.info("Bot stopped")
        graceful_shutdown(client, positions)
        if bs.prev_wallet_usdc is not None:
            try:
                r = await run_sync(process_interval_snapshot, client, bs, bs.intervals_passed + 1, False)
                if r["success"]:
                    bot_balance = r["bot_snap"]
            except Exception:
                pass
        pct = (bs.total_profit / INITIAL_BALANCE * 100) if INITIAL_BALANCE > 0 else 0
        log.info(f"Balance: ${INITIAL_BALANCE:.2f} -> ${bot_balance:.2f}")
        log.info(f"Profit: ${bs.total_profit:+.4f} ({pct:+.2f}%)")
        log.info(f"Intervals: {bs.intervals_passed}")
        log.info("-" * 40)
        if stats.early_trend_count > 0:
            et_wr = stats.early_trend_wins / (stats.early_trend_wins + stats.early_trend_losses) if (stats.early_trend_wins + stats.early_trend_losses) > 0 else 0
            log.info(f"  Early: {stats.early_trend_count} | W/L: {stats.early_trend_wins}/{stats.early_trend_losses} ({et_wr:.0%}) | PnL: ${stats.early_trend_pnl:+.2f}")
        if stats.vacuum_scalp_count > 0:
            vs_wr = stats.vacuum_scalp_wins / (stats.vacuum_scalp_wins + stats.vacuum_scalp_losses) if (stats.vacuum_scalp_wins + stats.vacuum_scalp_losses) > 0 else 0
            log.info(f"  Vacuum: {stats.vacuum_scalp_count} | W/L: {stats.vacuum_scalp_wins}/{stats.vacuum_scalp_losses} ({vs_wr:.0%}) | PnL: ${stats.vacuum_scalp_pnl:+.2f}")
        if stats.standard_count > 0:
            st_wr = stats.standard_wins / (stats.standard_wins + stats.standard_losses) if (stats.standard_wins + stats.standard_losses) > 0 else 0
            log.info(f"  Std:   {stats.standard_count} | W/L: {stats.standard_wins}/{stats.standard_losses} ({st_wr:.0%}) | PnL: ${stats.standard_pnl:+.2f}")
        log.info(f"  TP: {stats.partial_tps} | VacTP: {stats.vacuum_tps} | Trail: {stats.trailing_exits} | SL: {stats.stop_losses} | Exit: {stats.early_exits} | Exp: {stats.expired_count}")
        log.info(f"  TOTAL: {stats.total_trades} | WR: {stats.win_rate:.0%} | PnL: ${stats.total_pnl:+.2f}")
        log.info("=" * 60)
    finally:
        ws_rtds_task.cancel()
        ws_market_task.cancel()
        ws_user_task.cancel()
        ws_binance_direct_task.cancel()
        http = await get_http()
        await http.close()


def _is_running_in_event_loop():
    try:
        asyncio.get_running_loop()
        return True
    except RuntimeError:
        return False


_bot_task = None


def main():
    if _is_running_in_event_loop():
        print("Jupyter detected. Run: await main_async()")
        print("Or: start_background() / stop_bot()")
        return
    asyncio.run(main_async())


def start_background():
    global _bot_task
    if _bot_task and not _bot_task.done():
        print("Already running.")
        return _bot_task
    _bot_task = asyncio.get_event_loop().create_task(main_async())
    print("Bot started. Stop: stop_bot()")
    return _bot_task


def stop_bot():
    global _bot_task
    if _bot_task and not _bot_task.done():
        _bot_task.cancel()
        print("Stopping...")
    else:
        print("Not running.")


if __name__ == "__main__":
    main()