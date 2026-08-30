#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ASTER PERPETUAL BOT V1 - BTC / ETH / HYPE
=========================================

Motores:
  A) RANGE_1PCT: gatilho +/-1% do ponto zero, alvo +1%, hedge/recovery alternado,
     martingale financeiro 3x, protecao apos 3 falhas e rearmamento apos 3%.
  B) MACD: BTC/ETH/HYPE em 5m e 15m, MACD 7/21/9, entrada apenas no cruzamento
     confirmado em candle fechado, recovery 3x da perda acumulada e protecao
     apos 3 perdas consecutivas com deslocamento minimo de 3% + novo cruzamento.

Conta/margem:
  - Aster Pro USDT perpetual.
  - Hedge Mode obrigatorio.
  - ISOLATED obrigatorio.
  - Alavancagem adaptativa por ordem, consultando leverageBracket.
  - A API documentada aceita leverage 1..125. MAX_REQUESTED_LEVERAGE pode ser 150,
    mas o bot limita automaticamente ao menor valor entre 125 e o permitido pelo ativo.
  - O bot tambem limita leverage para manter distancia de liquidacao estimada acima do
    stop/protecao configurado. Com stop de 2%, 125x normalmente NAO sera seguro.

IMPORTANTE SOBRE "USD 10 por operacao":
  O codigo interpreta INITIAL_OPERATION_MARGIN_USD=10 como ORCAMENTO DE MARGEM da
  primeira entrada, e nao como notional. A exposicao (notional) = margem * leverage.
  Se voce quiser US$10 de NOTIONAL em vez de US$10 de margem, use
  OPERATION_VALUE_MODE=NOTIONAL.

Seguranca:
  - LIVE_TRADING=0 por padrao.
  - SOFT kill-switch bloqueia novas entradas, mas continua gerenciando posicoes.
  - HARD kill-switch cancela ordens e tenta fechar posicoes do bot.
  - Noticias de alto impacto (3 estrelas) bloqueiam entradas -15/+15 minutos.
  - Estado persistente em BOT_DIR/state.json.
  - Ordens usam clientOrderId prefixado para reconciliacao.

Dependencias:
  pip install requests websocket-client beautifulsoup4

Variaveis principais Railway:
  ASTER_USER_ADDRESS=0x...              # carteira principal/login Aster
  ASTER_API_WALLET_ADDRESS=0x...        # endereço público da API Wallet autorizada
  ASTER_API_WALLET_PRIVATE_KEY=0x...    # chave privada SOMENTE da API Wallet
  LIVE_TRADING=0
  VALIDATE_API_ONLY=1
  BOT_DIR=/data
  MAX_REQUESTED_LEVERAGE=150
  INITIAL_BANKROLL_USD=10
  INITIAL_OPERATION_MARGIN_USD=10
  OPERATION_VALUE_MODE=MARGIN
  RECOVERY_MULTIPLIER=3
  MAX_RECOVERY_FAILURES=3
  NEWS_FILTER_ENABLED=1
  NEWS_FAIL_CLOSED=1

Nao coloque seed phrase nem chave privada da Trust Wallet principal no Railway.
Use somente a chave privada da API Wallet dedicada e autorizada na Aster.
"""

from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import queue
import re
import signal
import sys
import threading
import time
import traceback
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from decimal import Decimal, ROUND_DOWN, ROUND_UP, getcontext
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import urlencode

import requests
from eth_account import Account
from eth_account.messages import encode_typed_data

try:
    import websocket  # websocket-client
except Exception:
    websocket = None

try:
    from bs4 import BeautifulSoup
except Exception:
    BeautifulSoup = None

getcontext().prec = 28
D = Decimal
UTC = timezone.utc

# -----------------------------------------------------------------------------
# CONFIG
# -----------------------------------------------------------------------------

VERSION = "2.0.2-v3"
BOT_NAME = "ASTER_PERPETUAL_BOT_V3"
BASE_URL = os.getenv("ASTER_BASE_URL", "https://fapi.asterdex.com").rstrip("/")
WS_BASE = os.getenv("ASTER_WS_BASE", "wss://fstream.asterdex.com").rstrip("/")
USER_ADDRESS = os.getenv("ASTER_USER_ADDRESS", "").strip()
SIGNER_ADDRESS = os.getenv("ASTER_API_WALLET_ADDRESS", "").strip()
SIGNER_PRIVATE_KEY = os.getenv("ASTER_API_WALLET_PRIVATE_KEY", "").strip()
LIVE_TRADING = os.getenv("LIVE_TRADING", "0") == "1"
VALIDATE_API_ONLY = os.getenv("VALIDATE_API_ONLY", "0") == "1"
BOT_DIR = Path(os.getenv("BOT_DIR", "/data"))
BOT_DIR.mkdir(parents=True, exist_ok=True)
STATE_FILE = BOT_DIR / "state.json"
TRADES_FILE = BOT_DIR / "trades.jsonl"
NEWS_CACHE_FILE = BOT_DIR / "news_calendar_cache.json"
LOG_FILE = BOT_DIR / "aster_bot.log"

SYMBOLS = tuple(s.strip().upper() for s in os.getenv("SYMBOLS", "BTCUSDT,ETHUSDT,HYPEUSDT").split(",") if s.strip())

INITIAL_BANKROLL_USD = D(os.getenv("INITIAL_BANKROLL_USD", "10"))
INITIAL_OPERATION_MARGIN_USD = D(os.getenv("INITIAL_OPERATION_MARGIN_USD", "10"))
OPERATION_VALUE_MODE = os.getenv("OPERATION_VALUE_MODE", "MARGIN").upper().strip()  # MARGIN|NOTIONAL
RECOVERY_MULTIPLIER = D(os.getenv("RECOVERY_MULTIPLIER", "3"))
MAX_RECOVERY_FAILURES = int(os.getenv("MAX_RECOVERY_FAILURES", "3"))

MAX_REQUESTED_LEVERAGE = int(os.getenv("MAX_REQUESTED_LEVERAGE", "150"))
API_HARD_MAX_LEVERAGE = 125
MIN_LEVERAGE = int(os.getenv("MIN_LEVERAGE", "1"))
LEVERAGE_HEADROOM = D(os.getenv("LEVERAGE_HEADROOM", "0.95"))
LIQUIDATION_BUFFER_PCT = D(os.getenv("LIQUIDATION_BUFFER_PCT", "0.005"))  # 0.5%
MIN_FREE_WALLET_BUFFER_USD = D(os.getenv("MIN_FREE_WALLET_BUFFER_USD", "1.00"))
MAX_MARGIN_FRACTION_PER_STRATEGY = D(os.getenv("MAX_MARGIN_FRACTION_PER_STRATEGY", "1.0"))

# Range engine
RANGE_TRIGGER_PCT = D(os.getenv("RANGE_TRIGGER_PCT", "0.01"))
RANGE_TAKE_PROFIT_PCT = D(os.getenv("RANGE_TAKE_PROFIT_PCT", "0.01"))
RANGE_HARD_STOP_PCT = D(os.getenv("RANGE_HARD_STOP_PCT", "0.02"))
RANGE_REARM_PCT = D(os.getenv("RANGE_REARM_PCT", "0.03"))
RANGE_ENGINE_ENABLED = os.getenv("RANGE_ENGINE_ENABLED", "1") == "1"

# MACD engine
MACD_ENGINE_ENABLED = os.getenv("MACD_ENGINE_ENABLED", "1") == "1"
MACD_FAST = int(os.getenv("MACD_FAST", "7"))
MACD_SLOW = int(os.getenv("MACD_SLOW", "21"))
MACD_SIGNAL = int(os.getenv("MACD_SIGNAL", "9"))
MACD_TIMEFRAMES = tuple(x.strip() for x in os.getenv("MACD_TIMEFRAMES", "5m,15m").split(",") if x.strip())
MACD_REARM_PCT = D(os.getenv("MACD_REARM_PCT", "0.03"))

# Trade execution
RECV_WINDOW = int(os.getenv("RECV_WINDOW", "5000"))
HTTP_TIMEOUT = float(os.getenv("HTTP_TIMEOUT", "10"))
ORDER_FILL_WAIT_SECONDS = float(os.getenv("ORDER_FILL_WAIT_SECONDS", "8"))
ORDER_POLL_SECONDS = float(os.getenv("ORDER_POLL_SECONDS", "0.4"))
MAIN_LOOP_SECONDS = float(os.getenv("MAIN_LOOP_SECONDS", "0.5"))
REST_PRICE_FALLBACK_SECONDS = float(os.getenv("REST_PRICE_FALLBACK_SECONDS", "5"))
HEARTBEAT_SECONDS = float(os.getenv("HEARTBEAT_SECONDS", "30"))
ACCOUNT_SYNC_SECONDS = float(os.getenv("ACCOUNT_SYNC_SECONDS", "10"))

# The same Aster Hedge side is aggregated by symbol. To preserve exact per-strategy
# accounting, default policy allows only one active strategy owner per symbol.
# Change to 1 only if you accept virtual-lot PnL attribution drift.
ALLOW_MULTI_STRATEGY_SAME_SYMBOL = os.getenv("ALLOW_MULTI_STRATEGY_SAME_SYMBOL", "0") == "1"

# News filter
NEWS_FILTER_ENABLED = os.getenv("NEWS_FILTER_ENABLED", "1") == "1"
NEWS_FAIL_CLOSED = os.getenv("NEWS_FAIL_CLOSED", "1") == "1"
NEWS_WINDOW_BEFORE_MIN = int(os.getenv("NEWS_WINDOW_BEFORE_MIN", "15"))
NEWS_WINDOW_AFTER_MIN = int(os.getenv("NEWS_WINDOW_AFTER_MIN", "15"))
NEWS_REFRESH_SECONDS = int(os.getenv("NEWS_REFRESH_SECONDS", "10800"))
NEWS_MAX_STALE_SECONDS = int(os.getenv("NEWS_MAX_STALE_SECONDS", "172800"))
NEWS_LOOKAHEAD_DAYS = int(os.getenv("NEWS_LOOKAHEAD_DAYS", "7"))
NEWS_MANUAL_EVENTS_UTC = os.getenv("NEWS_MANUAL_EVENTS_UTC", "").strip()

# Kill switch
KILL_SWITCH_ON_API_ERRORS = int(os.getenv("KILL_SWITCH_ON_API_ERRORS", "8"))
HARD_KILL_ON_POSITION_MISMATCH = os.getenv("HARD_KILL_ON_POSITION_MISMATCH", "0") == "1"

# Logging
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()

# -----------------------------------------------------------------------------
# LOGGING
# -----------------------------------------------------------------------------

logger = logging.getLogger(BOT_NAME)
logger.setLevel(getattr(logging, LOG_LEVEL, logging.INFO))
formatter = logging.Formatter("%(asctime)s | %(levelname)s | %(message)s")
sh = logging.StreamHandler(sys.stdout)
sh.setFormatter(formatter)
logger.addHandler(sh)
try:
    fh = logging.FileHandler(LOG_FILE)
    fh.setFormatter(formatter)
    logger.addHandler(fh)
except Exception:
    pass

# -----------------------------------------------------------------------------
# HELPERS
# -----------------------------------------------------------------------------

def now_ms() -> int:
    return int(time.time() * 1000)


def now_iso() -> str:
    return datetime.now(UTC).isoformat()


def dec(x: Any, default: str = "0") -> Decimal:
    try:
        return D(str(x))
    except Exception:
        return D(default)


def dstr(x: Decimal, places: int = 8) -> str:
    q = D(10) ** -places
    s = format(x.quantize(q), "f")
    return s.rstrip("0").rstrip(".") if "." in s else s


def atomic_json_write(path: Path, data: Dict[str, Any]) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
    os.replace(tmp, path)


def jsonl_append(path: Path, obj: Dict[str, Any]) -> None:
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(obj, ensure_ascii=False) + "\n")


def floor_step(value: Decimal, step: Decimal) -> Decimal:
    if step <= 0:
        return value
    return (value / step).to_integral_value(rounding=ROUND_DOWN) * step


def ceil_step(value: Decimal, step: Decimal) -> Decimal:
    if step <= 0:
        return value
    return (value / step).to_integral_value(rounding=ROUND_UP) * step


def pct_change(a: Decimal, b: Decimal) -> Decimal:
    if a == 0:
        return D(0)
    return (b / a) - D(1)


def ema(values: List[Decimal], period: int) -> List[Decimal]:
    if len(values) < period:
        return []
    k = D(2) / D(period + 1)
    out = [sum(values[:period]) / D(period)]
    for v in values[period:]:
        out.append(v * k + out[-1] * (D(1) - k))
    return out


def macd_series(closes: List[Decimal], fast: int, slow: int, sig: int) -> Tuple[List[Decimal], List[Decimal]]:
    if len(closes) < slow + sig + 3:
        return [], []
    ef = ema(closes, fast)
    es = ema(closes, slow)
    # ef starts earlier. align to slow EMA first point.
    offset = slow - fast
    ef2 = ef[offset:]
    n = min(len(ef2), len(es))
    m = [ef2[i] - es[i] for i in range(n)]
    s = ema(m, sig)
    if not s:
        return [], []
    m_aligned = m[sig - 1:]
    n2 = min(len(m_aligned), len(s))
    return m_aligned[-n2:], s[-n2:]


def get_macd_cross(closes: List[Decimal]) -> Optional[str]:
    m, s = macd_series(closes, MACD_FAST, MACD_SLOW, MACD_SIGNAL)
    if len(m) < 2 or len(s) < 2:
        return None
    if m[-2] <= s[-2] and m[-1] > s[-1]:
        return "LONG"
    if m[-2] >= s[-2] and m[-1] < s[-1]:
        return "SHORT"
    return None

# -----------------------------------------------------------------------------
# ASTER REST CLIENT
# -----------------------------------------------------------------------------

class AsterAPIError(RuntimeError):
    def __init__(self, message: str, code: Optional[int] = None, payload: Any = None):
        super().__init__(message)
        self.code = code
        self.payload = payload


class AsterClient:
    def __init__(self, user_address: str, signer_address: str, signer_private_key: str):
        self.user_address = user_address
        self.signer_address = signer_address
        self.signer_private_key = signer_private_key
        if self.signer_private_key:
            derived = Account.from_key(self.signer_private_key).address
            if self.signer_address and derived.lower() != self.signer_address.lower():
                raise AsterAPIError(
                    f"ASTER_API_WALLET_PRIVATE_KEY nao corresponde a ASTER_API_WALLET_ADDRESS "
                    f"(derivado={derived})"
                )
        self.s = requests.Session()
        self.s.headers.update({"User-Agent": f"{BOT_NAME}/{VERSION}"})
        self.time_offset_ms = 0
        self.api_error_streak = 0
        self._lock = threading.Lock()
        self._last_nonce = 0

    def _ts(self) -> int:
        return now_ms() + self.time_offset_ms

    def _nonce(self) -> int:
        with self._lock:
            candidate = self._ts() * 1000
            self._last_nonce = max(candidate, self._last_nonce + 1)
            return self._last_nonce

    def sync_time(self) -> None:
        t0 = now_ms()
        r = self.s.get(BASE_URL + "/fapi/v3/time", timeout=HTTP_TIMEOUT)
        r.raise_for_status()
        server = int(r.json()["serverTime"])
        t1 = now_ms()
        midpoint = (t0 + t1) // 2
        self.time_offset_ms = server - midpoint
        logger.info("TIME SYNC | offset_ms=%s", self.time_offset_ms)

    def _request(self, method: str, path: str, params: Optional[Dict[str, Any]] = None,
                 signed: bool = False, api_key_only: bool = False, retry_unknown: bool = False) -> Any:
        params = dict(params or {})
        if signed:
            if not self.user_address or not self.signer_address or not self.signer_private_key:
                raise AsterAPIError("Credenciais da API Wallet V3 ausentes")
            params["nonce"] = self._nonce()
            params["signer"] = self.signer_address
            qs = urlencode([(k, str(v).lower() if isinstance(v, bool) else str(v)) for k, v in params.items()])
            typed_data = {"types": {"EIP712Domain": [{"name": "name", "type": "string"}, {"name": "version", "type": "string"}, {"name": "chainId", "type": "uint256"}, {"name": "verifyingContract", "type": "address"}], "Message": [{"name": "msg", "type": "string"}]}, "primaryType": "Message", "domain": {"name": "AsterSignTransaction", "version": "1", "chainId": 1666, "verifyingContract": "0x0000000000000000000000000000000000000000"}, "message": {"msg": qs}}
            signable = encode_typed_data(full_message=typed_data)
            params["signature"] = Account.sign_message(signable, private_key=self.signer_private_key).signature.hex()
        url = BASE_URL + path
        try:
            r = self.s.request(method, url, params=params, timeout=HTTP_TIMEOUT)
            if r.status_code == 503 and not retry_unknown:
                # Aster documents 503 on order endpoints as UNKNOWN execution status.
                raise AsterAPIError("HTTP 503: status de execucao desconhecido; reconciliar por clientOrderId", 503, r.text)
            if r.status_code >= 400:
                try:
                    body = r.json()
                    code = body.get("code") if isinstance(body, dict) else None
                    msg = body.get("msg", r.text) if isinstance(body, dict) else r.text
                except Exception:
                    code, msg, body = None, r.text, r.text
                raise AsterAPIError(f"HTTP {r.status_code} | {msg}", code, body)
            self.api_error_streak = 0
            return r.json() if r.text else {}
        except AsterAPIError:
            self.api_error_streak += 1
            raise
        except Exception as e:
            self.api_error_streak += 1
            raise AsterAPIError(str(e)) from e

    # Public
    def exchange_info(self) -> Dict[str, Any]:
        return self._request("GET", "/fapi/v3/exchangeInfo")

    def price(self, symbol: str) -> Decimal:
        x = self._request("GET", "/fapi/v3/ticker/price", {"symbol": symbol})
        return dec(x.get("price"))

    def mark(self, symbol: str) -> Decimal:
        x = self._request("GET", "/fapi/v3/premiumIndex", {"symbol": symbol})
        return dec(x.get("markPrice") or x.get("price"))

    def klines(self, symbol: str, interval: str, limit: int = 100) -> List[List[Any]]:
        return self._request("GET", "/fapi/v3/klines", {"symbol": symbol, "interval": interval, "limit": limit})

    # Signed
    def position_mode(self) -> bool:
        x = self._request("GET", "/fapi/v3/positionSide/dual", signed=True)
        return bool(x.get("dualSidePosition"))

    def multi_assets_mode(self) -> bool:
        x = self._request("GET", "/fapi/v3/multiAssetsMargin", signed=True)
        return bool(x.get("multiAssetsMargin"))

    def set_single_asset_mode(self) -> None:
        if not self.multi_assets_mode():
            return
        try:
            self._request("POST", "/fapi/v3/multiAssetsMargin",
                          {"multiAssetsMargin": "false"}, signed=True)
        except AsterAPIError as e:
            raise RuntimeError(
                "Aster esta em Multi-Assets Mode e nao permitiu mudar automaticamente para "
                "Single-Asset Mode. Cancele ordens e feche posicoes manuais na conta/subconta, "
                "desative Multi-Assets Mode na interface Aster e faca novo deploy. "
                f"Erro original: {e}"
            ) from e
        if self.multi_assets_mode():
            raise RuntimeError("Aster continuou em Multi-Assets Mode apos a solicitacao de desativacao")

    def set_hedge_mode(self) -> None:
        try:
            self._request("POST", "/fapi/v3/positionSide/dual", {"dualSidePosition": "true"}, signed=True)
        except AsterAPIError as e:
            # "No need to change" type errors are harmless; verify afterwards.
            if e.code not in (-4059,):
                raise

    def set_margin_type(self, symbol: str, isolated: bool = True) -> None:
        try:
            self._request("POST", "/fapi/v3/marginType",
                          {"symbol": symbol, "marginType": "ISOLATED" if isolated else "CROSSED"}, signed=True)
        except AsterAPIError as e:
            if e.code not in (-4046,):  # no need to change margin type
                raise

    def set_leverage(self, symbol: str, leverage: int) -> Dict[str, Any]:
        return self._request("POST", "/fapi/v3/leverage", {"symbol": symbol, "leverage": int(leverage)}, signed=True)

    def leverage_bracket(self, symbol: str) -> Any:
        return self._request("GET", "/fapi/v3/leverageBracket", {"symbol": symbol}, signed=True)

    def balance(self) -> Any:
        # Binance-compatible endpoint used by Aster Pro API.
        return self._request("GET", "/fapi/v3/balance", signed=True)

    def account(self) -> Any:
        return self._request("GET", "/fapi/v3/accountWithJoinMargin", signed=True)

    def positions(self, symbol: Optional[str] = None) -> Any:
        p = {"symbol": symbol} if symbol else {}
        return self._request("GET", "/fapi/v3/positionRisk", p, signed=True)

    def open_orders(self, symbol: Optional[str] = None) -> Any:
        p = {"symbol": symbol} if symbol else {}
        return self._request("GET", "/fapi/v3/openOrders", p, signed=True)

    def query_order(self, symbol: str, client_id: str) -> Dict[str, Any]:
        return self._request("GET", "/fapi/v3/order", {"symbol": symbol, "origClientOrderId": client_id}, signed=True)

    def order(self, symbol: str, side: str, position_side: str, quantity: Decimal,
              client_id: str, order_type: str = "MARKET") -> Dict[str, Any]:
        p = {
            "symbol": symbol,
            "side": side,
            "positionSide": position_side,
            "type": order_type,
            "quantity": dstr(quantity, 12),
            "newClientOrderId": client_id[:36],
            "newOrderRespType": "RESULT",
        }
        try:
            return self._request("POST", "/fapi/v3/order", p, signed=True)
        except AsterAPIError as e:
            if e.code == 503:
                # Never blindly retry. Reconcile first using deterministic client id.
                for _ in range(10):
                    time.sleep(0.5)
                    try:
                        return self.query_order(symbol, client_id)
                    except Exception:
                        continue
            raise

    def cancel_all(self, symbol: str) -> Any:
        return self._request("DELETE", "/fapi/v3/allOpenOrders", {"symbol": symbol}, signed=True)

    def income(self, symbol: Optional[str] = None, start_ms: Optional[int] = None, limit: int = 1000) -> Any:
        p: Dict[str, Any] = {"limit": limit}
        if symbol:
            p["symbol"] = symbol
        if start_ms:
            p["startTime"] = start_ms
        return self._request("GET", "/fapi/v3/income", p, signed=True)

# -----------------------------------------------------------------------------
# EXCHANGE SYMBOL RULES
# -----------------------------------------------------------------------------

@dataclass
class SymbolRules:
    symbol: str
    tick_size: Decimal
    step_size: Decimal
    min_qty: Decimal
    max_qty: Decimal
    min_notional: Decimal


class RulesBook:
    def __init__(self, client: AsterClient):
        self.client = client
        self.rules: Dict[str, SymbolRules] = {}

    def refresh(self) -> None:
        info = self.client.exchange_info()
        out: Dict[str, SymbolRules] = {}
        for s in info.get("symbols", []):
            sym = str(s.get("symbol", "")).upper()
            if sym not in SYMBOLS:
                continue
            tick = step = min_qty = min_notional = D(0)
            max_qty = D("1e50")
            for f in s.get("filters", []):
                ft = f.get("filterType")
                if ft == "PRICE_FILTER":
                    tick = dec(f.get("tickSize"))
                elif ft in ("LOT_SIZE", "MARKET_LOT_SIZE"):
                    # Prefer LOT_SIZE; market filter can be narrower. Use max constraints conservatively.
                    st = dec(f.get("stepSize"))
                    mn = dec(f.get("minQty"))
                    mx = dec(f.get("maxQty"), "1e50")
                    if st > step:
                        step = st
                    if mn > min_qty:
                        min_qty = mn
                    if mx < max_qty:
                        max_qty = mx
                elif ft in ("MIN_NOTIONAL", "NOTIONAL"):
                    min_notional = max(min_notional, dec(f.get("notional") or f.get("minNotional")))
            out[sym] = SymbolRules(sym, tick or D("0.00000001"), step or D("0.00000001"),
                                   min_qty, max_qty, min_notional)
        missing = [s for s in SYMBOLS if s not in out]
        if missing:
            raise RuntimeError(f"Simbolos nao disponiveis na Aster: {missing}")
        self.rules = out
        for r in out.values():
            logger.info("RULES | %s | tick=%s step=%s min_qty=%s min_notional=%s",
                        r.symbol, r.tick_size, r.step_size, r.min_qty, r.min_notional)

    def qty(self, symbol: str, raw: Decimal, price: Decimal) -> Decimal:
        r = self.rules[symbol]
        q = floor_step(raw, r.step_size)
        if q < r.min_qty:
            q = ceil_step(r.min_qty, r.step_size)
        if r.min_notional > 0 and q * price < r.min_notional:
            q = ceil_step(r.min_notional / price, r.step_size)
        if q > r.max_qty:
            raise RuntimeError(f"Quantidade acima maxQty {symbol}: {q}>{r.max_qty}")
        return q

# -----------------------------------------------------------------------------
# MARKET DATA WEBSOCKET + REST FALLBACK
# -----------------------------------------------------------------------------

class MarketData:
    def __init__(self, client: AsterClient):
        self.client = client
        self.prices: Dict[str, Decimal] = {}
        self.price_ts: Dict[str, float] = {}
        self._lock = threading.Lock()
        self.stop = threading.Event()
        self.ws_thread: Optional[threading.Thread] = None
        self.rest_thread: Optional[threading.Thread] = None

    def start(self) -> None:
        if websocket is not None:
            self.ws_thread = threading.Thread(target=self._ws_loop, name="market-ws", daemon=True)
            self.ws_thread.start()
        else:
            logger.warning("websocket-client ausente; usando REST fallback")
        self.rest_thread = threading.Thread(target=self._rest_loop, name="market-rest", daemon=True)
        self.rest_thread.start()

    def get(self, symbol: str, max_age: float = 4.0) -> Optional[Decimal]:
        with self._lock:
            p = self.prices.get(symbol)
            ts = self.price_ts.get(symbol, 0)
        if p is not None and time.time() - ts <= max_age:
            return p
        try:
            p = self.client.price(symbol)
            self._set(symbol, p)
            return p
        except Exception as e:
            logger.warning("PRICE FALLBACK FAIL | %s | %s", symbol, e)
            return p

    def _set(self, symbol: str, price: Decimal) -> None:
        if price <= 0:
            return
        with self._lock:
            self.prices[symbol] = price
            self.price_ts[symbol] = time.time()

    def _ws_loop(self) -> None:
        streams = "/".join(f"{s.lower()}@miniTicker" for s in SYMBOLS)
        url = f"{WS_BASE}/stream?streams={streams}"
        while not self.stop.is_set():
            try:
                def on_message(ws, message):
                    try:
                        j = json.loads(message)
                        data = j.get("data", j)
                        sym = str(data.get("s", "")).upper()
                        p = dec(data.get("c"))
                        if sym in SYMBOLS and p > 0:
                            self._set(sym, p)
                    except Exception:
                        pass

                def on_open(ws):
                    logger.info("MARKET WS | CONECTADO | %s", url)

                def on_error(ws, error):
                    logger.warning("MARKET WS | erro=%s", error)

                def on_close(ws, code, msg):
                    logger.warning("MARKET WS | fechado code=%s msg=%s", code, msg)

                app = websocket.WebSocketApp(url, on_open=on_open, on_message=on_message,
                                             on_error=on_error, on_close=on_close)
                app.run_forever(ping_interval=120, ping_timeout=30)
            except Exception as e:
                logger.warning("MARKET WS LOOP | %s", e)
            if not self.stop.wait(3):
                continue

    def _rest_loop(self) -> None:
        while not self.stop.wait(REST_PRICE_FALLBACK_SECONDS):
            for sym in SYMBOLS:
                with self._lock:
                    age = time.time() - self.price_ts.get(sym, 0)
                if age < REST_PRICE_FALLBACK_SECONDS:
                    continue
                try:
                    self._set(sym, self.client.price(sym))
                except Exception as e:
                    logger.warning("REST PRICE | %s | %s", sym, e)

# -----------------------------------------------------------------------------
# NEWS FILTER - Investing 3-star/high importance + cache/manual fallback
# -----------------------------------------------------------------------------

class NewsFilter:
    def __init__(self):
        self.events: List[Dict[str, Any]] = []
        self.last_refresh = 0.0
        self.last_success = 0.0
        self.stop = threading.Event()
        self.thread: Optional[threading.Thread] = None
        self._lock = threading.Lock()
        self._load_cache()
        self._load_manual()

    def _load_cache(self) -> None:
        try:
            j = json.loads(NEWS_CACHE_FILE.read_text(encoding="utf-8"))
            self.events = j.get("events", [])
            self.last_success = float(j.get("last_success", 0))
        except Exception:
            pass

    def _load_manual(self) -> None:
        # Format: 2026-08-30T12:30:00Z|US CPI;2026-09-01T14:00:00Z|ISM
        if not NEWS_MANUAL_EVENTS_UTC:
            return
        manual = []
        for item in NEWS_MANUAL_EVENTS_UTC.split(";"):
            if not item.strip():
                continue
            parts = item.split("|", 1)
            try:
                dt = datetime.fromisoformat(parts[0].replace("Z", "+00:00")).astimezone(UTC)
                manual.append({"ts": dt.timestamp(), "title": parts[1] if len(parts) > 1 else "MANUAL", "source": "MANUAL"})
            except Exception:
                continue
        if manual:
            self.events.extend(manual)

    def start(self) -> None:
        if not NEWS_FILTER_ENABLED:
            return
        self.thread = threading.Thread(target=self._loop, name="news", daemon=True)
        self.thread.start()

    def _loop(self) -> None:
        while not self.stop.is_set():
            try:
                self.refresh()
            except Exception as e:
                logger.warning("NEWS | refresh falhou | %s", e)
            self.stop.wait(NEWS_REFRESH_SECONDS)

    def refresh(self) -> None:
        self.last_refresh = time.time()
        events = self._fetch_investing()
        if not events:
            raise RuntimeError("Investing nao retornou eventos 3 estrelas")
        with self._lock:
            manual = [e for e in self.events if e.get("source") == "MANUAL"]
            self.events = events + manual
            self.last_success = time.time()
            atomic_json_write(NEWS_CACHE_FILE, {"last_success": self.last_success, "events": self.events})
        logger.info("NEWS | cache atualizado | eventos_high=%s", len(events))

    def _fetch_investing(self) -> List[Dict[str, Any]]:
        if BeautifulSoup is None:
            raise RuntimeError("beautifulsoup4 ausente")
        # Public webpage; Investing does not expose a documented public API. We parse
        # only timestamp/title/high-impact markers and retain cache if page changes.
        url = "https://www.investing.com/economic-calendar/"
        headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/151 Safari/537.36",
            "Accept-Language": "en-US,en;q=0.9",
        }
        r = requests.get(url, headers=headers, timeout=15)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
        events: List[Dict[str, Any]] = []
        horizon = datetime.now(UTC) + timedelta(days=NEWS_LOOKAHEAD_DAYS)
        # Legacy + current variants. High impact commonly exposed as sentiment-3/bull3.
        rows = soup.find_all(["tr", "article", "div"])
        for row in rows:
            txt = " ".join(row.stripped_strings)
            cls = " ".join(row.get("class", []) if hasattr(row, "get") else [])
            html = str(row)[:5000]
            high = bool(re.search(r"sentiment[-_ ]?3|bull3|high[ -]?impact|three[ -]?stars|3-star", cls + " " + html, re.I))
            if not high:
                # aria labels sometimes carry importance.
                high = "High Volatility Expected" in txt
            if not high:
                continue
            raw_dt = None
            for attr in ("data-event-datetime", "data-datetime", "datetime"):
                if hasattr(row, "get") and row.get(attr):
                    raw_dt = row.get(attr)
                    break
                node = row.find(attrs={attr: True}) if hasattr(row, "find") else None
                if node:
                    raw_dt = node.get(attr)
                    break
            if not raw_dt:
                m = re.search(r'data-event-datetime=["\']([^"\']+)', html)
                raw_dt = m.group(1) if m else None
            if not raw_dt:
                continue
            dt = self._parse_investing_dt(raw_dt)
            if not dt:
                continue
            if dt < datetime.now(UTC) - timedelta(hours=2) or dt > horizon:
                continue
            title = txt[:240] or "High-impact event"
            events.append({"ts": dt.timestamp(), "title": title, "source": "INVESTING_3STAR"})
        # dedupe
        unique = {}
        for e in events:
            unique[(round(float(e["ts"])), e["title"][:80])] = e
        return sorted(unique.values(), key=lambda x: x["ts"])

    @staticmethod
    def _parse_investing_dt(raw: str) -> Optional[datetime]:
        raw = raw.strip()
        fmts = ["%Y/%m/%d %H:%M:%S", "%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S%z"]
        for fmt in fmts:
            try:
                dt = datetime.strptime(raw, fmt)
                # Investing page may emit site-local times. Prefer explicit offset. If no
                # offset, treat as UTC only when parser cannot infer. Users can supply
                # manual events for critical releases if the page format changes.
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=UTC)
                return dt.astimezone(UTC)
            except Exception:
                pass
        try:
            dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=UTC)
            return dt.astimezone(UTC)
        except Exception:
            return None

    def blocked(self, when: Optional[datetime] = None) -> Tuple[bool, Optional[str]]:
        if not NEWS_FILTER_ENABLED:
            return False, None
        when = when or datetime.now(UTC)
        with self._lock:
            events = list(self.events)
            last_success = self.last_success
        stale = (time.time() - last_success) > NEWS_MAX_STALE_SECONDS if last_success else True
        if stale and NEWS_FAIL_CLOSED:
            return True, "NEWS_CACHE_STALE_FAIL_CLOSED"
        ts = when.timestamp()
        before = NEWS_WINDOW_BEFORE_MIN * 60
        after = NEWS_WINDOW_AFTER_MIN * 60
        for e in events:
            et = float(e.get("ts", 0))
            if et - before <= ts <= et + after:
                return True, f"{e.get('source')} | {e.get('title')}"
        return False, None

# -----------------------------------------------------------------------------
# STATE
# -----------------------------------------------------------------------------

def empty_range_state(symbol: str) -> Dict[str, Any]:
    return {
        "strategy": f"RANGE:{symbol}",
        "symbol": symbol,
        "equity": str(INITIAL_BANKROLL_USD),
        "anchor": None,
        "status": "IDLE",  # IDLE|BASKET|PROTECT
        "basket": None,
        "recovery_deficit": "0",
        "failures": 0,
        "protect_anchor": None,
        "wins": 0,
        "losses": 0,
        "realized_pnl": "0",
        "last_result": "NONE",
        "last_update": now_iso(),
    }


def empty_macd_state(symbol: str, tf: str) -> Dict[str, Any]:
    return {
        "strategy": f"MACD:{symbol}:{tf}",
        "symbol": symbol,
        "tf": tf,
        "equity": str(INITIAL_BANKROLL_USD),
        "position": None,
        "recovery_deficit": "0",
        "loss_streak": 0,
        "protect": False,
        "protect_anchor": None,
        "last_candle_close_ms": 0,
        "wins": 0,
        "losses": 0,
        "realized_pnl": "0",
        "last_result": "NONE",
        "last_update": now_iso(),
    }


def fresh_state() -> Dict[str, Any]:
    return {
        "version": VERSION,
        "created_at": now_iso(),
        "updated_at": now_iso(),
        "kill_switch": {"mode": "OFF", "reason": None, "at": None},
        "range": {s: empty_range_state(s) for s in SYMBOLS},
        "macd": {f"{s}:{tf}": empty_macd_state(s, tf) for s in SYMBOLS for tf in MACD_TIMEFRAMES},
        "symbol_owner": {s: None for s in SYMBOLS},
        "last_wallet": {},
    }


class StateStore:
    def __init__(self):
        self.lock = threading.RLock()
        self.state = self._load()

    def _load(self) -> Dict[str, Any]:
        try:
            st = json.loads(STATE_FILE.read_text(encoding="utf-8"))
            logger.info("STATE | carregado | %s", STATE_FILE)
        except Exception:
            st = fresh_state()
            logger.info("STATE | novo")
        # Non-destructive migrations / add new configured symbols/timeframes.
        st.setdefault("kill_switch", {"mode": "OFF", "reason": None, "at": None})
        st.setdefault("range", {})
        st.setdefault("macd", {})
        st.setdefault("symbol_owner", {})
        st.setdefault("last_wallet", {})
        for s in SYMBOLS:
            st["range"].setdefault(s, empty_range_state(s))
            st["symbol_owner"].setdefault(s, None)
            for tf in MACD_TIMEFRAMES:
                st["macd"].setdefault(f"{s}:{tf}", empty_macd_state(s, tf))
        st["version"] = VERSION
        return st

    def save(self) -> None:
        with self.lock:
            self.state["updated_at"] = now_iso()
            atomic_json_write(STATE_FILE, self.state)

    def kill(self, mode: str, reason: str) -> None:
        with self.lock:
            self.state["kill_switch"] = {"mode": mode, "reason": reason, "at": now_iso()}
            self.save()
        logger.error("KILL SWITCH | mode=%s | reason=%s", mode, reason)

    def killed(self) -> str:
        with self.lock:
            return self.state.get("kill_switch", {}).get("mode", "OFF")

# -----------------------------------------------------------------------------
# ACCOUNT / LEVERAGE / EXECUTION
# -----------------------------------------------------------------------------

class AccountManager:
    def __init__(self, client: AsterClient, rules: RulesBook, store: StateStore):
        self.client = client
        self.rules = rules
        self.store = store
        self.wallet_balance = D(0)
        self.available_balance = D(0)
        self.unrealized = D(0)
        self.last_sync = 0.0
        self.commission: Dict[str, Decimal] = {}
        self._lock = threading.RLock()

    def sync(self, force: bool = False) -> None:
        if not LIVE_TRADING and not VALIDATE_API_ONLY:
            strategy_count = (
                (len(SYMBOLS) if RANGE_ENGINE_ENABLED else 0)
                + (len(SYMBOLS) * len(MACD_TIMEFRAMES) if MACD_ENGINE_ENABLED else 0)
            )
            simulated_total = INITIAL_BANKROLL_USD * D(max(1, strategy_count))
            self.wallet_balance = simulated_total
            self.available_balance = simulated_total
            self.unrealized = D(0)
            self.last_sync = time.time()
            return
        if not force and time.time() - self.last_sync < ACCOUNT_SYNC_SECONDS:
            return
        with self._lock:
            acct = self.client.account()
            self.wallet_balance = dec(acct.get("totalWalletBalance") or acct.get("totalMarginBalance") or 0)
            self.available_balance = dec(acct.get("availableBalance") or 0)
            self.unrealized = dec(acct.get("totalUnrealizedProfit") or 0)
            self.last_sync = time.time()
            with self.store.lock:
                self.store.state["last_wallet"] = {
                    "wallet": str(self.wallet_balance),
                    "available": str(self.available_balance),
                    "unrealized": str(self.unrealized),
                    "at": now_iso(),
                }
            self.store.save()

    def free_margin(self) -> Decimal:
        self.sync()
        return max(D(0), self.available_balance - MIN_FREE_WALLET_BUFFER_USD)

    def ensure_modes(self) -> None:
        if not LIVE_TRADING:
            logger.info("MODES | simulacao: nao altera Hedge/Isolated")
            return
        self.client.set_single_asset_mode()
        logger.info("MODES | Single-Asset Mode confirmado")
        self.client.set_hedge_mode()
        if not self.client.position_mode():
            raise RuntimeError("Conta nao esta em Hedge Mode")
        for s in SYMBOLS:
            self.client.set_margin_type(s, True)
        logger.info("MODES | Hedge Mode confirmado | ISOLATED solicitado em %s", ",".join(SYMBOLS))

    def get_brackets(self, symbol: str) -> List[Dict[str, Any]]:
        if not LIVE_TRADING:
            return []
        try:
            x = self.client.leverage_bracket(symbol)
            if isinstance(x, list):
                if x and "brackets" in x[0]:
                    return x[0].get("brackets", [])
                return x
            if isinstance(x, dict):
                return x.get("brackets", [])
        except Exception as e:
            logger.warning("LEVERAGE BRACKET FAIL | %s | %s", symbol, e)
        return []

    def max_exchange_leverage(self, symbol: str, notional: Decimal) -> Tuple[int, Decimal]:
        brackets = self.get_brackets(symbol)
        max_lev = API_HARD_MAX_LEVERAGE
        mmr = D("0.005")  # conservative fallback
        if brackets:
            chosen = None
            for b in brackets:
                floor = dec(b.get("notionalFloor"))
                cap = dec(b.get("notionalCap"), "1e50")
                if floor <= notional < cap:
                    chosen = b
                    break
            if chosen is None:
                chosen = brackets[-1]
            max_lev = int(chosen.get("initialLeverage", max_lev))
            mmr = dec(chosen.get("maintMarginRatio"), "0.005")
        return max(1, min(max_lev, API_HARD_MAX_LEVERAGE, MAX_REQUESTED_LEVERAGE)), mmr

    def safe_leverage_cap(self, symbol: str, notional: Decimal, adverse_distance_pct: Decimal) -> Tuple[int, Dict[str, Any]]:
        exch_max, mmr = self.max_exchange_leverage(symbol, notional)
        # Approx isolated liquidation-distance safety model:
        # initial margin rate ~= 1/L. Require 1/L > adverse_move + mmr + buffer.
        denom = adverse_distance_pct + mmr + LIQUIDATION_BUFFER_PCT
        liq_safe = int((D(1) / denom).to_integral_value(rounding=ROUND_DOWN)) if denom > 0 else exch_max
        cap = max(MIN_LEVERAGE, min(exch_max, liq_safe, API_HARD_MAX_LEVERAGE, MAX_REQUESTED_LEVERAGE))
        return cap, {"exchange_max": exch_max, "mmr": str(mmr), "liq_safe_max": liq_safe, "denom": str(denom)}

    def base_margin_budget(self, strategy_state: Dict[str, Any]) -> Decimal:
        eq = dec(strategy_state.get("equity"), str(INITIAL_BANKROLL_USD))
        # User rule: if equity > 10, use 100% of current logical cash as initial budget.
        desired = max(INITIAL_OPERATION_MARGIN_USD, eq)
        desired = min(desired, eq * MAX_MARGIN_FRACTION_PER_STRATEGY)
        return max(D(0), desired)

    def sizing_for_profit_target(self, symbol: str, price: Decimal, strategy_state: Dict[str, Any],
                                 target_profit: Optional[Decimal], target_move_pct: Decimal,
                                 adverse_distance_pct: Decimal) -> Optional[Dict[str, Any]]:
        self.sync()
        logical_eq = dec(strategy_state.get("equity"), str(INITIAL_BANKROLL_USD))
        physical_free = self.free_margin()
        if logical_eq <= 0 or physical_free <= 0:
            return None

        base_budget = min(self.base_margin_budget(strategy_state), logical_eq, physical_free)
        if base_budget <= 0:
            return None

        if target_profit is None or target_profit <= 0:
            # Fresh operation: use the configured base value and highest safe leverage.
            if OPERATION_VALUE_MODE == "NOTIONAL":
                desired_notional = max(INITIAL_OPERATION_MARGIN_USD, logical_eq)
                cap, meta = self.safe_leverage_cap(symbol, desired_notional, adverse_distance_pct)
                margin = desired_notional / D(cap)
                if margin > base_budget:
                    return None
                lev = cap
            else:
                # Need an estimate, iterate because bracket max can depend on notional.
                lev = min(MAX_REQUESTED_LEVERAGE, API_HARD_MAX_LEVERAGE)
                desired_notional = base_budget * D(lev)
                cap, meta = self.safe_leverage_cap(symbol, desired_notional, adverse_distance_pct)
                lev = cap
                desired_notional = base_budget * D(lev)
                margin = base_budget
        else:
            # Need target_profit net-ish over target movement. Add taker entry+exit fee reserve.
            # Official base taker can differ by tier; default 0.035% each side configurable.
            taker = D(os.getenv("TAKER_FEE_RATE", "0.00035"))
            effective_move = target_move_pct - (taker * D(2))
            if effective_move <= 0:
                return None
            desired_notional = target_profit / effective_move
            cap, meta = self.safe_leverage_cap(symbol, desired_notional, adverse_distance_pct)
            # Minimum leverage required to fit within available margin budget.
            req = int((desired_notional / base_budget).to_integral_value(rounding=ROUND_UP))
            if req > cap:
                logger.warning("SIZING NAO CABE | %s | target_profit=%s desired_notional=%s margin_budget=%s lev_req=%s lev_cap=%s meta=%s",
                               symbol, target_profit, desired_notional, base_budget, req, cap, meta)
                return None
            lev = max(MIN_LEVERAGE, req)
            margin = desired_notional / D(lev)
            # Use only necessary margin, not all cash, during recovery.

        lev = max(MIN_LEVERAGE, min(int(lev), MAX_REQUESTED_LEVERAGE, API_HARD_MAX_LEVERAGE))
        notional = desired_notional if target_profit else (margin * D(lev))
        qty = self.rules.qty(symbol, notional / price, price)
        actual_notional = qty * price
        actual_margin = actual_notional / D(lev)
        if actual_margin > physical_free or actual_margin > logical_eq:
            return None
        return {
            "leverage": lev,
            "qty": qty,
            "price": price,
            "notional": actual_notional,
            "margin": actual_margin,
            "target_profit": target_profit or D(0),
            "meta": meta,
        }

    def set_leverage(self, symbol: str, leverage: int) -> None:
        if LIVE_TRADING:
            self.client.set_leverage(symbol, leverage)
        logger.info("LEVERAGE | %s | %sx", symbol, leverage)

# -----------------------------------------------------------------------------
# EXECUTION + VIRTUAL LOT BOOK
# -----------------------------------------------------------------------------

class ExecutionEngine:
    PREFIX = "a2"

    def __init__(self, client: AsterClient, account: AccountManager, rules: RulesBook, store: StateStore):
        self.client = client
        self.account = account
        self.rules = rules
        self.store = store
        self.seq = 0
        self.lock = threading.RLock()

    def client_id(self, strategy_id: str, action: str) -> str:
        self.seq = (self.seq + 1) % 9999
        digest = hashlib.sha1(strategy_id.encode()).hexdigest()[:6]
        return f"{self.PREFIX}-{digest}-{action[:5]}-{int(time.time())%1000000}-{self.seq}"[:36]

    @staticmethod
    def order_side(position_side: str, opening: bool) -> str:
        if position_side == "LONG":
            return "BUY" if opening else "SELL"
        return "SELL" if opening else "BUY"

    def _fill_from_response(self, symbol: str, resp: Dict[str, Any], client_id: str, fallback_price: Decimal) -> Tuple[Decimal, Decimal]:
        status = str(resp.get("status", ""))
        qty = dec(resp.get("executedQty") or resp.get("origQty"))
        avg = dec(resp.get("avgPrice") or resp.get("price"))
        end = time.time() + ORDER_FILL_WAIT_SECONDS
        while (status not in ("FILLED", "PARTIALLY_FILLED") or qty <= 0 or avg <= 0) and time.time() < end:
            try:
                q = self.client.query_order(symbol, client_id)
                status = str(q.get("status", status))
                qty = dec(q.get("executedQty") or q.get("origQty") or qty)
                avg = dec(q.get("avgPrice") or q.get("price") or avg)
                resp = q
                if status == "FILLED" and qty > 0:
                    break
            except Exception:
                pass
            time.sleep(ORDER_POLL_SECONDS)
        if qty <= 0:
            raise RuntimeError(f"Ordem sem fill confirmado: {symbol} client_id={client_id} status={status}")
        if avg <= 0:
            avg = fallback_price
        return qty, avg

    def market(self, strategy_id: str, symbol: str, position_side: str, qty: Decimal,
               opening: bool, ref_price: Decimal) -> Dict[str, Any]:
        side = self.order_side(position_side, opening)
        cid = self.client_id(strategy_id, "open" if opening else "close")
        if not LIVE_TRADING:
            logger.info("SIM ORDER | %s | %s %s posSide=%s qty=%s px~%s cid=%s",
                        strategy_id, "OPEN" if opening else "CLOSE", side, position_side, qty, ref_price, cid)
            return {"qty": qty, "price": ref_price, "client_id": cid, "order_id": f"SIM-{cid}", "status": "FILLED", "time": now_ms()}
        resp = self.client.order(symbol, side, position_side, qty, cid, "MARKET")
        filled, avg = self._fill_from_response(symbol, resp, cid, ref_price)
        logger.info("ORDER FILLED | %s | %s %s posSide=%s qty=%s avg=%s cid=%s",
                    strategy_id, "OPEN" if opening else "CLOSE", side, position_side, filled, avg, cid)
        return {"qty": filled, "price": avg, "client_id": cid, "order_id": resp.get("orderId"), "status": resp.get("status"), "time": now_ms()}

    def open_leg(self, strategy_id: str, symbol: str, position_side: str, sizing: Dict[str, Any],
                 reason: str) -> Dict[str, Any]:
        self.account.set_leverage(symbol, sizing["leverage"])
        fill = self.market(strategy_id, symbol, position_side, sizing["qty"], True, sizing["price"])
        leg = {
            "id": fill["client_id"],
            "side": position_side,
            "qty": str(fill["qty"]),
            "entry_price": str(fill["price"]),
            "leverage": sizing["leverage"],
            "notional": str(fill["qty"] * fill["price"]),
            "margin_est": str((fill["qty"] * fill["price"]) / D(sizing["leverage"])),
            "opened_at": now_iso(),
            "reason": reason,
        }
        jsonl_append(TRADES_FILE, {"event": "OPEN", "strategy": strategy_id, "symbol": symbol, "leg": leg, "at": now_iso()})
        return leg

    def close_leg(self, strategy_id: str, symbol: str, leg: Dict[str, Any], ref_price: Decimal, reason: str) -> Dict[str, Any]:
        qty = dec(leg["qty"])
        fill = self.market(strategy_id, symbol, leg["side"], qty, False, ref_price)
        entry = dec(leg["entry_price"])
        exitp = fill["price"]
        closed_qty = min(qty, fill["qty"])
        gross = (exitp - entry) * closed_qty if leg["side"] == "LONG" else (entry - exitp) * closed_qty
        fee_rate = D(os.getenv("TAKER_FEE_RATE", "0.00035"))
        fees_est = (entry * closed_qty + exitp * closed_qty) * fee_rate
        pnl = gross - fees_est
        rec = {
            "leg_id": leg["id"], "side": leg["side"], "qty": str(closed_qty),
            "entry_price": str(entry), "exit_price": str(exitp), "gross": str(gross),
            "fees_est": str(fees_est), "pnl_est": str(pnl), "reason": reason,
            "closed_at": now_iso(), "close_client_id": fill["client_id"],
        }
        jsonl_append(TRADES_FILE, {"event": "CLOSE", "strategy": strategy_id, "symbol": symbol, "close": rec, "at": now_iso()})
        return rec

    def close_legs(self, strategy_id: str, symbol: str, legs: List[Dict[str, Any]], ref_price: Decimal, reason: str) -> Tuple[Decimal, List[Dict[str, Any]]]:
        # Close both sides near-simultaneously: execute larger notional winner/loser sequentially under lock.
        # API batch order could be used, but per-order reconciliation is safer on HTTP 503 UNKNOWN.
        closes = []
        total = D(0)
        for leg in list(legs):
            try:
                c = self.close_leg(strategy_id, symbol, leg, ref_price, reason)
                closes.append(c)
                total += dec(c["pnl_est"])
            except Exception as e:
                logger.exception("CLOSE LEG FAIL | %s | leg=%s | %s", strategy_id, leg.get("id"), e)
                raise
        return total, closes

# -----------------------------------------------------------------------------
# OWNERSHIP / INTERFERENCE CONTROL
# -----------------------------------------------------------------------------

def acquire_owner(store: StateStore, symbol: str, strategy_id: str) -> bool:
    if ALLOW_MULTI_STRATEGY_SAME_SYMBOL:
        return True
    with store.lock:
        owner = store.state["symbol_owner"].get(symbol)
        if owner in (None, strategy_id):
            store.state["symbol_owner"][symbol] = strategy_id
            store.save()
            return True
        return False


def release_owner(store: StateStore, symbol: str, strategy_id: str) -> None:
    if ALLOW_MULTI_STRATEGY_SAME_SYMBOL:
        return
    with store.lock:
        if store.state["symbol_owner"].get(symbol) == strategy_id:
            store.state["symbol_owner"][symbol] = None
            store.save()

# -----------------------------------------------------------------------------
# RANGE +/-1% ENGINE
# -----------------------------------------------------------------------------

class RangeEngine:
    def __init__(self, symbol: str, client: AsterClient, md: MarketData, news: NewsFilter,
                 account: AccountManager, exe: ExecutionEngine, store: StateStore):
        self.symbol = symbol
        self.id = f"RANGE:{symbol}"
        self.client = client
        self.md = md
        self.news = news
        self.account = account
        self.exe = exe
        self.store = store

    def st(self) -> Dict[str, Any]:
        return self.store.state["range"][self.symbol]

    def _new_anchor(self, price: Decimal) -> None:
        st = self.st()
        st["anchor"] = str(price)
        st["status"] = "IDLE"
        st["basket"] = None
        st["failures"] = 0
        st["protect_anchor"] = None
        st["last_update"] = now_iso()
        self.store.save()
        release_owner(self.store, self.symbol, self.id)
        logger.info("RANGE ANCHOR | %s | anchor=%s", self.symbol, price)

    def _target_recovery_profit(self, st: Dict[str, Any], basket: Optional[Dict[str, Any]] = None) -> Decimal:
        rd = dec(st.get("recovery_deficit"))
        if basket:
            # Add current estimated basket loss at trigger price if negative.
            pass
        return rd * RECOVERY_MULTIPLIER if rd > 0 else D(0)

    @staticmethod
    def unrealized(legs: List[Dict[str, Any]], price: Decimal) -> Decimal:
        total = D(0)
        for leg in legs:
            q = dec(leg["qty"]); ep = dec(leg["entry_price"])
            total += (price - ep) * q if leg["side"] == "LONG" else (ep - price) * q
        return total

    def _open(self, side: str, price: Decimal, target_profit: Optional[Decimal], reason: str) -> Optional[Dict[str, Any]]:
        st = self.st()
        blocked, why = self.news.blocked()
        if blocked:
            logger.info("RANGE BLOQUEADO NEWS | %s | %s", self.symbol, why)
            return None
        if self.store.killed() != "OFF":
            return None
        if not acquire_owner(self.store, self.symbol, self.id):
            logger.info("RANGE BLOQUEADO OWNER | %s | owner=%s", self.symbol, self.store.state["symbol_owner"].get(self.symbol))
            return None
        sizing = self.account.sizing_for_profit_target(
            self.symbol, price, st, target_profit, RANGE_TAKE_PROFIT_PCT, RANGE_HARD_STOP_PCT
        )
        if not sizing:
            logger.warning("RANGE SIZING NAO CABE | %s | target=%s", self.symbol, target_profit)
            return None
        logger.info("RANGE SIZING | %s | side=%s target=%s lev=%sx notional=%s margin=%s qty=%s meta=%s",
                    self.symbol, side, target_profit, sizing["leverage"], sizing["notional"], sizing["margin"], sizing["qty"], sizing["meta"])
        return self.exe.open_leg(self.id, self.symbol, side, sizing, reason)

    def _start_basket(self, side: str, price: Decimal) -> None:
        st = self.st()
        rd = dec(st.get("recovery_deficit"))
        target = rd * RECOVERY_MULTIPLIER if rd > 0 else None
        leg = self._open(side, price, target, "RANGE_INITIAL" if rd == 0 else "RANGE_REARM_RECOVERY")
        if not leg:
            return
        anchor = dec(st["anchor"])
        st["status"] = "BASKET"
        st["basket"] = {
            "origin_anchor": str(anchor),
            "initial_side": side,
            "initial_entry": str(price),
            "legs": [leg],
            "active_side": side,
            "alternations": 0,
            # Current opposite trigger is zero/origin anchor.
            "next_reverse_price": str(anchor),
            "tp_price": str(price * (D(1) + RANGE_TAKE_PROFIT_PCT) if side == "LONG" else price * (D(1) - RANGE_TAKE_PROFIT_PCT)),
            "hard_stop_price": str(price * (D(1) - RANGE_HARD_STOP_PCT) if side == "LONG" else price * (D(1) + RANGE_HARD_STOP_PCT)),
            "started_at": now_iso(),
        }
        st["last_update"] = now_iso()
        self.store.save()
        logger.info("RANGE BASKET START | %s | %s @ %s | anchor=%s", self.symbol, side, price, anchor)

    def _close_basket(self, price: Decimal, reason: str, protect_after: bool = False) -> None:
        st = self.st(); b = st.get("basket")
        if not b:
            return
        pnl, closes = self.exe.close_legs(self.id, self.symbol, b.get("legs", []), price, reason)
        before = dec(st.get("equity"))
        after = before + pnl
        st["equity"] = str(after)
        st["realized_pnl"] = str(dec(st.get("realized_pnl")) + pnl)
        rd_before = dec(st.get("recovery_deficit"))
        if pnl < 0:
            rd_after = rd_before + (-pnl)
            st["losses"] = int(st.get("losses", 0)) + 1
            st["last_result"] = "LOSS"
        elif pnl > 0:
            rd_after = max(D(0), rd_before - pnl)
            st["wins"] = int(st.get("wins", 0)) + 1
            st["last_result"] = "WIN"
        else:
            rd_after = rd_before
            st["last_result"] = "FLAT"
        st["recovery_deficit"] = str(rd_after)
        st["basket"] = None
        st["failures"] = 0
        if protect_after:
            st["status"] = "PROTECT"
            st["protect_anchor"] = str(price)
            st["anchor"] = str(price)
        else:
            st["status"] = "IDLE"
            st["anchor"] = str(price)
            st["protect_anchor"] = None
        st["last_update"] = now_iso()
        self.store.save()
        release_owner(self.store, self.symbol, self.id)
        logger.info("RANGE CLOSE | %s | reason=%s pnl=%s equity=%s RD %s->%s protect=%s",
                    self.symbol, reason, pnl, after, rd_before, rd_after, protect_after)

    def _reverse(self, price: Decimal) -> None:
        st = self.st(); b = st.get("basket")
        if not b:
            return
        current = b["active_side"]
        new_side = "SHORT" if current == "LONG" else "LONG"
        # Loss to be recovered = official recovery deficit + current basket negative MTM.
        mtm = self.unrealized(b["legs"], price)
        accumulated_loss = dec(st.get("recovery_deficit")) + max(D(0), -mtm)
        target = accumulated_loss * RECOVERY_MULTIPLIER
        if target <= 0:
            target = None
        leg = self._open(new_side, price, target, "RANGE_ALTERNATING_RECOVERY")
        if not leg:
            return
        b["legs"].append(leg)
        b["active_side"] = new_side
        b["alternations"] = int(b.get("alternations", 0)) + 1
        st["failures"] = b["alternations"]
        # Alternate between origin anchor and initial entry, matching user's examples.
        if new_side == b["initial_side"]:
            b["next_reverse_price"] = b["origin_anchor"]
        else:
            b["next_reverse_price"] = b["initial_entry"]
        # Recovery leg seeks 1% in its favor. When hit, close all legs together.
        b["recovery_tp_price"] = str(price * (D(1) + RANGE_TAKE_PROFIT_PCT) if new_side == "LONG" else price * (D(1) - RANGE_TAKE_PROFIT_PCT))
        st["last_update"] = now_iso()
        self.store.save()
        logger.warning("RANGE REVERSE | %s | new=%s @%s | mtm=%s accumulated_loss=%s target3x=%s failures=%s",
                       self.symbol, new_side, price, mtm, accumulated_loss, target, st["failures"])
        if b["alternations"] >= MAX_RECOVERY_FAILURES:
            # User protection: after 3 wrong alternations close all and wait 3%.
            self._close_basket(price, "MAX_3_RECOVERY_FAILURES", protect_after=True)

    def tick(self, price: Decimal) -> None:
        with self.store.lock:
            st = self.st()
            if st.get("anchor") is None:
                self._new_anchor(price)
                return
            status = st.get("status", "IDLE")
            anchor = dec(st["anchor"])
            if status == "PROTECT":
                pa = dec(st.get("protect_anchor") or anchor)
                move = abs(pct_change(pa, price))
                if move >= RANGE_REARM_PCT:
                    # Rearm with current price as new zero. Recovery deficit remains.
                    st["status"] = "IDLE"
                    st["anchor"] = str(price)
                    st["protect_anchor"] = None
                    st["failures"] = 0
                    self.store.save()
                    logger.info("RANGE PROTECT LIBERADO | %s | move=%s | new_anchor=%s | RD=%s",
                                self.symbol, move, price, st["recovery_deficit"])
                return

            if status == "IDLE":
                up = anchor * (D(1) + RANGE_TRIGGER_PCT)
                dn = anchor * (D(1) - RANGE_TRIGGER_PCT)
                if price >= up:
                    self._start_basket("LONG", price)
                elif price <= dn:
                    self._start_basket("SHORT", price)
                return

            b = st.get("basket")
            if not b:
                st["status"] = "IDLE"; self.store.save(); return

            active = b["active_side"]
            alternations = int(b.get("alternations", 0))
            if alternations == 0:
                tp = dec(b["tp_price"])
                hard = dec(b["hard_stop_price"])
                if (active == "LONG" and price >= tp) or (active == "SHORT" and price <= tp):
                    self._close_basket(price, "INITIAL_TP_1PCT", protect_after=False)
                    return
                # Hard stop only if price jumps through reversal/hedge mechanics.
                if (b["initial_side"] == "LONG" and price <= hard) or (b["initial_side"] == "SHORT" and price >= hard):
                    self._close_basket(price, "INITIAL_HARD_STOP_2PCT", protect_after=True)
                    return
            else:
                rtp = dec(b.get("recovery_tp_price"))
                if rtp > 0 and ((active == "LONG" and price >= rtp) or (active == "SHORT" and price <= rtp)):
                    self._close_basket(price, "RECOVERY_LEG_TP_1PCT_CLOSE_ALL", protect_after=False)
                    return

            rev = dec(b["next_reverse_price"])
            # Crossing reverse boundary in direction opposite active leg.
            if (active == "LONG" and price <= rev) or (active == "SHORT" and price >= rev):
                self._reverse(price)

# -----------------------------------------------------------------------------
# MACD ENGINE 5m/15m
# -----------------------------------------------------------------------------

class MacdEngine:
    def __init__(self, symbol: str, tf: str, client: AsterClient, md: MarketData, news: NewsFilter,
                 account: AccountManager, exe: ExecutionEngine, store: StateStore):
        self.symbol = symbol; self.tf = tf
        self.id = f"MACD:{symbol}:{tf}"
        self.client = client; self.md = md; self.news = news; self.account = account; self.exe = exe; self.store = store

    def st(self) -> Dict[str, Any]:
        return self.store.state["macd"][f"{self.symbol}:{self.tf}"]

    def closed_closes(self) -> Tuple[List[Decimal], int]:
        rows = self.client.klines(self.symbol, self.tf, max(100, MACD_SLOW + MACD_SIGNAL + 20))
        if not rows:
            return [], 0
        # Last kline may be open. Close time field index 6.
        n = now_ms()
        closed = [r for r in rows if int(r[6]) < n]
        if not closed:
            return [], 0
        return [dec(r[4]) for r in closed], int(closed[-1][6])

    def _close(self, price: Decimal, reason: str) -> None:
        st = self.st(); pos = st.get("position")
        if not pos:
            return
        c = self.exe.close_leg(self.id, self.symbol, pos["leg"], price, reason)
        pnl = dec(c["pnl_est"])
        eq = dec(st["equity"]) + pnl
        st["equity"] = str(eq)
        st["realized_pnl"] = str(dec(st.get("realized_pnl")) + pnl)
        rd = dec(st.get("recovery_deficit"))
        if pnl < 0:
            rd += -pnl
            st["loss_streak"] = int(st.get("loss_streak", 0)) + 1
            st["losses"] = int(st.get("losses", 0)) + 1
            st["last_result"] = "LOSS"
        elif pnl > 0:
            rd = max(D(0), rd - pnl)
            st["wins"] = int(st.get("wins", 0)) + 1
            st["last_result"] = "WIN"
            if rd == 0:
                st["loss_streak"] = 0
        else:
            st["last_result"] = "FLAT"
        st["recovery_deficit"] = str(rd)
        st["position"] = None
        if int(st.get("loss_streak", 0)) >= MAX_RECOVERY_FAILURES:
            st["protect"] = True
            st["protect_anchor"] = str(price)
        st["last_update"] = now_iso()
        self.store.save()
        release_owner(self.store, self.symbol, self.id)
        logger.info("MACD CLOSE | %s | %s | pnl=%s eq=%s RD=%s streak=%s protect=%s",
                    self.id, reason, pnl, eq, rd, st["loss_streak"], st["protect"])

    def _open(self, side: str, price: Decimal) -> None:
        st = self.st()
        blocked, why = self.news.blocked()
        if blocked:
            logger.info("MACD NEWS BLOCK | %s | %s", self.id, why); return
        if self.store.killed() != "OFF": return
        if not acquire_owner(self.store, self.symbol, self.id):
            logger.info("MACD OWNER BLOCK | %s | owner=%s", self.id, self.store.state["symbol_owner"].get(self.symbol)); return
        rd = dec(st.get("recovery_deficit"))
        target = rd * RECOVERY_MULTIPLIER if rd > 0 else None
        # MACD has no fixed TP; use 1% as sizing recovery objective, while actual exit is opposite cross.
        sizing = self.account.sizing_for_profit_target(self.symbol, price, st, target, D("0.01"), D("0.02"))
        if not sizing:
            logger.warning("MACD SIZING NAO CABE | %s | target=%s", self.id, target); return
        leg = self.exe.open_leg(self.id, self.symbol, side, sizing, "MACD_CROSS")
        st["position"] = {"side": side, "leg": leg, "opened_at": now_iso()}
        st["last_update"] = now_iso()
        self.store.save()
        logger.info("MACD OPEN | %s | %s @%s | lev=%sx qty=%s target3x=%s",
                    self.id, side, price, sizing["leverage"], sizing["qty"], target)

    def tick(self, price: Decimal) -> None:
        st = self.st()
        try:
            closes, close_ms = self.closed_closes()
        except Exception as e:
            logger.warning("MACD KLINES FAIL | %s | %s", self.id, e); return
        if close_ms <= int(st.get("last_candle_close_ms", 0)):
            return
        st["last_candle_close_ms"] = close_ms
        cross = get_macd_cross(closes)
        self.store.save()
        if not cross:
            return
        logger.info("MACD CROSS | %s | cross=%s close_ms=%s price=%s", self.id, cross, close_ms, price)

        if st.get("protect"):
            pa = dec(st.get("protect_anchor"))
            if pa <= 0:
                st["protect_anchor"] = str(price); self.store.save(); return
            if abs(pct_change(pa, price)) < MACD_REARM_PCT:
                logger.info("MACD PROTECT | %s | falta deslocamento 3%% | move=%s", self.id, abs(pct_change(pa, price)))
                return
            # User requires 3% + aligned crossing. Current cross is the alignment.
            st["protect"] = False
            st["loss_streak"] = 0
            st["protect_anchor"] = None
            self.store.save()
            logger.info("MACD PROTECT LIBERADO | %s | cross=%s", self.id, cross)

        pos = st.get("position")
        if pos:
            if pos["side"] == cross:
                return
            # Opposite confirmed cross closes current. Only after close may open new recovery position.
            self._close(price, "OPPOSITE_MACD_CROSS")
            st = self.st()
            if st.get("protect"):
                return
            self._open(cross, price)
        else:
            self._open(cross, price)

# -----------------------------------------------------------------------------
# STARTUP RECONCILIATION + KILL SWITCH
# -----------------------------------------------------------------------------

class Reconciler:
    def __init__(self, client: AsterClient, store: StateStore):
        self.client = client; self.store = store

    def expected_by_symbol_side(self) -> Dict[Tuple[str, str], Decimal]:
        out: Dict[Tuple[str, str], Decimal] = {}
        with self.store.lock:
            for sym, st in self.store.state["range"].items():
                b = st.get("basket")
                if b:
                    for leg in b.get("legs", []):
                        key = (sym, leg["side"])
                        out[key] = out.get(key, D(0)) + dec(leg["qty"])
            for key, st in self.store.state["macd"].items():
                pos = st.get("position")
                if pos:
                    leg = pos["leg"]
                    k = (st["symbol"], leg["side"])
                    out[k] = out.get(k, D(0)) + dec(leg["qty"])
        return out

    def reconcile(self) -> bool:
        if not LIVE_TRADING:
            return True
        expected = self.expected_by_symbol_side()
        actual: Dict[Tuple[str, str], Decimal] = {}
        pos = self.client.positions()
        for p in pos:
            sym = str(p.get("symbol", "")).upper(); ps = str(p.get("positionSide", ""))
            if sym not in SYMBOLS or ps not in ("LONG", "SHORT"):
                continue
            q = abs(dec(p.get("positionAmt")))
            if q > 0:
                actual[(sym, ps)] = q
        mismatches = []
        keys = set(expected) | set(actual)
        for k in keys:
            e = expected.get(k, D(0)); a = actual.get(k, D(0))
            # tolerate one minimal step.
            tol = D("0.00000001")
            if abs(e - a) > tol:
                mismatches.append((k, e, a))
        if mismatches:
            reason = f"POSITION_MISMATCH expected_vs_actual={mismatches}"
            self.store.kill("HARD" if HARD_KILL_ON_POSITION_MISMATCH else "SOFT", reason)
            return False
        logger.info("RECONCILE | OK | positions=%s", actual)
        return True

# -----------------------------------------------------------------------------
# BOT
# -----------------------------------------------------------------------------

class Bot:
    def __init__(self):
        self.stop = threading.Event()
        self.client = AsterClient(USER_ADDRESS, SIGNER_ADDRESS, SIGNER_PRIVATE_KEY)
        self.store = StateStore()
        self.rules = RulesBook(self.client)
        self.md = MarketData(self.client)
        self.news = NewsFilter()
        self.account = AccountManager(self.client, self.rules, self.store)
        self.exe = ExecutionEngine(self.client, self.account, self.rules, self.store)
        self.reconciler = Reconciler(self.client, self.store)
        self.range_engines: List[RangeEngine] = []
        self.macd_engines: List[MacdEngine] = []
        self.last_hb = 0.0

    def startup(self) -> None:
        logger.info("=" * 90)
        logger.info("%s | version=%s | LIVE_TRADING=%s", BOT_NAME, VERSION, LIVE_TRADING)
        logger.info("SYMBOLS=%s | RANGE=%s | MACD=%s | TF=%s", SYMBOLS, RANGE_ENGINE_ENABLED, MACD_ENGINE_ENABLED, MACD_TIMEFRAMES)
        logger.info("MARGIN=ISOLATED | MODE=HEDGE | MAX_REQUESTED_LEV=%s | API_HARD_CAP=%s", MAX_REQUESTED_LEVERAGE, API_HARD_MAX_LEVERAGE)
        logger.info("BANKROLL_LOGICO=%s por estrategia | INITIAL_OPERATION=%s mode=%s | RECOVERY=%sx | MAX_FAIL=%s",
                    INITIAL_BANKROLL_USD, INITIAL_OPERATION_MARGIN_USD, OPERATION_VALUE_MODE, RECOVERY_MULTIPLIER, MAX_RECOVERY_FAILURES)
        logger.info("NEWS 3-STAR=%s | janela=-%sm/+%sm | fail_closed=%s", NEWS_FILTER_ENABLED, NEWS_WINDOW_BEFORE_MIN, NEWS_WINDOW_AFTER_MIN, NEWS_FAIL_CLOSED)
        logger.info("SAME_SYMBOL_MULTI_STRATEGY=%s (0 preserva contabilidade exata da posicao agregada Aster)", ALLOW_MULTI_STRATEGY_SAME_SYMBOL)
        logger.info("=" * 90)
        if (LIVE_TRADING or VALIDATE_API_ONLY) and (not USER_ADDRESS or not SIGNER_ADDRESS or not SIGNER_PRIVATE_KEY):
            raise RuntimeError("LIVE_TRADING=1 ou VALIDATE_API_ONLY=1 requer as tres credenciais da API Wallet V3")
        self.client.sync_time()
        self.rules.refresh()
        if VALIDATE_API_ONLY:
            mode = self.client.position_mode()
            multi_assets = self.client.multi_assets_mode()
            balances = self.client.balance()
            account = self.client.account()
            positions = self.client.positions()
            logger.info("API V3 VALIDADA | signer=%s | hedge=%s | multi_assets=%s | balances=%s | positions=%s | canTrade=%s",
                        SIGNER_ADDRESS, mode, multi_assets, len(balances) if isinstance(balances, list) else 0,
                        len(positions) if isinstance(positions, list) else 0,
                        account.get("canTrade") if isinstance(account, dict) else None)
            return
        if LIVE_TRADING:
            self.account.ensure_modes()
            self.account.sync(force=True)
            self.reconciler.reconcile()
        else:
            logger.warning("MODO SIMULACAO: nenhuma ordem real sera enviada")

        if RANGE_ENGINE_ENABLED:
            self.range_engines = [RangeEngine(s, self.client, self.md, self.news, self.account, self.exe, self.store) for s in SYMBOLS]
        if MACD_ENGINE_ENABLED:
            self.macd_engines = [MacdEngine(s, tf, self.client, self.md, self.news, self.account, self.exe, self.store)
                                 for s in SYMBOLS for tf in MACD_TIMEFRAMES]
        self.md.start(); self.news.start()

    def hard_kill(self) -> None:
        if not LIVE_TRADING:
            return
        logger.error("HARD KILL EXECUTION | cancelando ordens e fechando posicoes conhecidas")
        for s in SYMBOLS:
            try: self.client.cancel_all(s)
            except Exception as e: logger.error("HARD KILL cancel %s | %s", s, e)
        # Close only positions represented in bot state through engines to avoid touching unknown manual positions.
        for e in self.range_engines:
            try:
                st = e.st(); b = st.get("basket")
                p = self.md.get(e.symbol)
                if b and p: e._close_basket(p, "HARD_KILL", protect_after=True)
            except Exception as ex: logger.exception("HARD KILL range %s | %s", e.symbol, ex)
        for e in self.macd_engines:
            try:
                st = e.st(); p = self.md.get(e.symbol)
                if st.get("position") and p: e._close(p, "HARD_KILL")
            except Exception as ex: logger.exception("HARD KILL macd %s | %s", e.id, ex)

    def heartbeat(self) -> None:
        if time.time() - self.last_hb < HEARTBEAT_SECONDS:
            return
        self.last_hb = time.time()
        try:
            if LIVE_TRADING: self.account.sync(force=True)
        except Exception as e:
            logger.warning("HEARTBEAT account sync | %s", e)
        parts = []
        with self.store.lock:
            for s in SYMBOLS:
                r = self.store.state["range"][s]
                parts.append(f"R:{s}:eq={r['equity']},RD={r['recovery_deficit']},status={r['status']},fail={r['failures']}")
            for key, m in self.store.state["macd"].items():
                if m["symbol"] in SYMBOLS and m["tf"] in MACD_TIMEFRAMES:
                    parts.append(f"M:{m['symbol']}:{m['tf']}:eq={m['equity']},RD={m['recovery_deficit']},streak={m['loss_streak']},pos={'1' if m.get('position') else '0'},prot={int(bool(m.get('protect')))}")
            ks = self.store.state["kill_switch"]
        logger.info("HEARTBEAT | wallet=%s avail=%s unreal=%s | kill=%s:%s | %s",
                    self.account.wallet_balance, self.account.available_balance, self.account.unrealized,
                    ks.get("mode"), ks.get("reason"), " | ".join(parts))

    def run(self) -> None:
        self.startup()
        if VALIDATE_API_ONLY:
            logger.info("VALIDATE_API_ONLY concluido; encerrando sem alterar configuracoes e sem enviar ordens")
            self.shutdown()
            return
        while not self.stop.is_set():
            try:
                if self.client.api_error_streak >= KILL_SWITCH_ON_API_ERRORS and self.store.killed() == "OFF":
                    self.store.kill("SOFT", f"API_ERROR_STREAK={self.client.api_error_streak}")
                if self.store.killed() == "HARD":
                    self.hard_kill()
                    self.store.kill("SOFT", "HARD_KILL_EXECUTED; manual review required")
                prices = {s: self.md.get(s) for s in SYMBOLS}
                for e in self.range_engines:
                    p = prices.get(e.symbol)
                    if p and p > 0:
                        try: e.tick(p)
                        except Exception as ex: logger.exception("RANGE TICK FAIL | %s | %s", e.symbol, ex)
                for e in self.macd_engines:
                    p = prices.get(e.symbol)
                    if p and p > 0:
                        try: e.tick(p)
                        except Exception as ex: logger.exception("MACD TICK FAIL | %s | %s", e.id, ex)
                self.heartbeat()
            except KeyboardInterrupt:
                break
            except Exception as e:
                logger.exception("MAIN LOOP | %s", e)
            self.stop.wait(MAIN_LOOP_SECONDS)
        self.shutdown()

    def shutdown(self) -> None:
        logger.info("SHUTDOWN | salvando estado")
        self.store.save()
        self.md.stop.set(); self.news.stop.set(); self.stop.set()


def main() -> None:
    bot = Bot()
    def _sig(signum, frame):
        logger.warning("SIGNAL %s recebido", signum)
        bot.stop.set()
    signal.signal(signal.SIGINT, _sig)
    signal.signal(signal.SIGTERM, _sig)
    bot.run()


if __name__ == "__main__":
    main()
