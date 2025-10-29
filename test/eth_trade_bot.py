#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ETH perpetual trading bot for OKX.

说明（中文）：
- 启动时使用 REST 加载合约元信息、账户余额并转换为 USDT。
- 运行时优先使用 WebSocket 更新持仓、余额、订单与行情：订阅私有频道 positions、balance_and_position、orders，可选 fills；公共频道使用 tickers。
- 下单支持 REST 与 WS 两种发送方式（默认使用 REST），提供批量下单与批量撤单的封装，且在发送前自动限速。
- active_orders 以 orders WS 推送为最终来源；WS 的 op="order"/"batch-orders"/"cancel-order"/"batch-cancel-orders" 的直接响应也会被记录并与 active_orders 关联。
- 提供 Mock 模式（USE_MOCK=1）便于离线测试。

使用：
- 通过环境变量设置 OKX API：OKX_API_KEY, OKX_SECRET_KEY, OKX_PASSPHRASE
- OKX_FLAG=1 为模拟盘，=0 为实盘
- USE_MOCK=1 使用内置 Mock API，不连接外部服务（推荐初次测试）

作者备注：
- 请先在模拟盘或 USE_MOCK=1 下完成测试，再在实盘运行。
- 切勿在公开场景中泄露 API Secret/Passphrase。
"""

import asyncio
import time
import json
import logging
import string
import random
import os
from datetime import datetime
from collections import defaultdict
from decimal import Decimal, getcontext, ROUND_HALF_UP
from typing import Optional, Dict, Any, List

# 尝试导入 OKX SDK（私有与公共 WS、Account/Trade/Market）
try:
    from okx.websocket.WsPrivateAsync import WsPrivateAsync as PrivateWs
except Exception:
    PrivateWs = None
try:
    from okx.websocket.WsPublicAsync import WsPublicAsync as PublicWs
except Exception:
    PublicWs = None

try:
    import okx.Account as Account
    import okx.Trade as Trade
    import okx.MarketData as MarketData
except Exception:
    Account = None
    Trade = None
    MarketData = None

getcontext().prec = 28

# -------------------- 配置 & 默认值 --------------------
USE_MOCK = os.getenv("USE_MOCK", "0") == "1"

API_KEY = os.getenv("OKX_API_KEY", "")
SECRET_KEY = os.getenv("OKX_SECRET_KEY", "")
PASSPHRASE = os.getenv("OKX_PASSPHRASE", "")

OKX_FLAG = os.getenv("OKX_FLAG", "1")  # "1" testnet, "0" live

RUN_FOREVER = True

CONTRACT_INFO: Dict[str, Any] = {
    "symbol": "ETH-USDT-SWAP",
    "lotSz": 1,
    "minSz": 0.0,     # will be fetched
    "ctVal": 0.0,     # will be fetched (contract face value)
    "tickSz": 0.0,    # will be fetched
    "ctValCcy": "ETH",
    "instType": "SWAP",
    "instIdCode": None,
    "instFamily": None
}
SYMBOL = CONTRACT_INFO["symbol"]
TICK_SIZE = CONTRACT_INFO["tickSz"]

TRADE_STRATEGY = {
    "price_offset": 0.015,
    "eth_position": 0.01,
    "leverage": 10,
    "order_increment": 0,
    "fixed_trend_direction": "long",
    "trend_mode": "fixed"
}

# -------------------- 日志 --------------------
LOG_DIR = "logs"
os.makedirs(LOG_DIR, exist_ok=True)
LOG_FILE = os.path.join(LOG_DIR, "trading.log")

logger = logging.getLogger("eth_trade_bot")
logger.setLevel(logging.DEBUG)
if not logger.handlers:
    fh = logging.FileHandler(LOG_FILE)
    fh.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
    ch = logging.StreamHandler()
    ch.setFormatter(logging.Formatter('%(message)s'))
    logger.addHandler(fh)
    logger.addHandler(ch)


def log_action(action: str, details: str, level: str = "info", extra_data: Optional[dict] = None, exc_info: bool = False):
    symbols = {"debug": "🔵", "info": "🟢", "warning": "🟠", "error": "🔴", "critical": "⛔"}
    symbol = symbols.get(level, "⚪")
    header = "\n" + "-" * 80 + "\n" + f"[{datetime.now().strftime('%H:%M:%S.%f')}] {symbol} {action}"
    line = header + f"\n  • {details}"
    if extra_data is not None:
        try:
            line += f"\n  • 附加数据: {json.dumps(extra_data, ensure_ascii=False, indent=2)}"
        except Exception:
            line += f"\n  • 附加数据: {extra_data}"
    line += "\n" + "-" * 80
    if level == "debug":
        logger.debug(line, exc_info=exc_info)
    elif level == "warning":
        logger.warning(line, exc_info=exc_info)
    elif level == "error":
        logger.error(line, exc_info=exc_info)
    elif level == "critical":
        logger.critical(line, exc_info=exc_info)
    else:
        logger.info(line, exc_info=exc_info)


# -------------------- 全局运行时状态 --------------------
# 账户 USDT 等价总额
account_equity_usdt: float = 0.0
initial_equity_usdt: float = 0.0

# 价格与来源
current_price: float = 0.0
last_price: float = 0.0
price_source: str = "unknown"
last_ws_price_update: float = 0.0
last_api_price_update: float = 0.0

trading_direction = TRADE_STRATEGY.get("fixed_trend_direction", "long")
INSTRUMENTS_LOADED = False

# 订单 / 仓位 存储
active_orders: Dict[str, dict] = {}
order_pair_mapping: Dict[str, dict] = {}
position_info = defaultdict(lambda: {"pos": 0.0, "usdt_value": 0.0, "avg_px": 0.0, "upl": 0.0, "entry_time": 0})

# API clients（initialize_clients 填充）
account_api = None
trade_api = None
market_api = None

# 私有 WS 实例
_ws_instance = None

# 公共 WS 实例（tickers）
_public_ws_instance = None

# seen 去重集合（WS orders / fills）
seen_trade_ids = set()
seen_filled_ordids = set()
seen_reqids = set()

# public tickers 最优价记录
best_bid: float = 0.0
best_ask: float = 0.0

# 是否启用公共行情 WS
ENABLE_PUBLIC_TICKER = True
# 是否订阅 fills 频道（需 VIP5+）
ENABLE_FILLS_CHANNEL = False

# -------------------- 工具函数 --------------------
def safe_float(v, default: float = 0.0) -> float:
    try:
        if v is None or v == "":
            return default
        return float(v)
    except Exception:
        return default


def generate_order_id(prefix: str) -> str:
    clean = ''.join(c for c in prefix if c.isalnum())
    suffix = ''.join(random.choices(string.ascii_letters + string.digits, k=12))
    ts = int(time.time() * 1000) % 1000000
    return (clean + str(ts) + suffix)[:32]


def round_price(price: float) -> float:
    tick_val = CONTRACT_INFO.get("tickSz", 0) or TICK_SIZE or 0
    try:
        tick = Decimal(str(tick_val))
        p = Decimal(str(price))
        if tick == 0:
            return float(p)
        quant = (p / tick).quantize(Decimal("1"), rounding=ROUND_HALF_UP)
        rounded = (quant * tick).normalize()
        return float(rounded)
    except Exception:
        return float(price)


def round_to_min_size(size: float) -> float:
    min_sz = CONTRACT_INFO.get("minSz", 0) or 0
    try:
        m = Decimal(str(min_sz))
        s = Decimal(str(size))
        if m == 0:
            return float(s)
        q = (s / m).quantize(Decimal("1"), rounding=ROUND_HALF_UP)
        rounded = (q * m).normalize()
        return float(rounded)
    except Exception:
        return float(size)


def validate_position_size(sz: float) -> float:
    """
    校验下单数量，若小于 minSz 则抛异常或调整为 minSz。
    当前策略：若小于 minSz，则调整到 minSz；你也可以改为抛错终止下单。
    """
    min_sz = CONTRACT_INFO.get("minSz", 0) or 0
    if min_sz <= 0:
        return sz
    if sz <= 0:
        raise ValueError("下单数量必须大于 0")
    # 若小于最小单位，调整为最小单位
    if sz < min_sz:
        sz = min_sz
    return sz


# -------------------- Mock APIs（便于本地测试） --------------------
class MockTradeAPI:
    def place_order(self, **kwargs):
        return {"code": "0", "data": [{"ordId": f"mock_{int(time.time() * 1000)}", "clOrdId": kwargs.get("clOrdId", "")}]}

    def place_multiple_orders(self, batch):
        return {"code": "0", "data": [{"clOrdId": r.get("clOrdId", ""), "sCode": "0", "ordId": f"mock_{random.randint(1000, 9999)}"} for r in batch]}

    def cancel_order(self, **kwargs):
        return {"code": "0", "data": []}

    def cancel_multiple_orders(self, requests):
        return {"code": "0", "data": []}


class MockAccountAPI:
    def get_account_balance(self, **kwargs):
        # return sample balances: USDT and BTC
        return {"code": "0", "data": [{"details": [{"ccy": "USDT", "eq": "1000.0"}, {"ccy": "BTC", "eq": "0.01"}]}]}

    def get_positions(self, **kwargs):
        return {"code": "0", "data": []}

    def get_instruments(self, **kwargs):
        return {
            "code": "0",
            "data": [
                {
                    "instId": CONTRACT_INFO["symbol"],
                    "minSz": "0.01",
                    "tickSz": "0.01",
                    "ctVal": "0.1",
                    "lotSz": "0.01",
                    "ctValCcy": "ETH",
                    "instIdCode": "2021032601102994",
                    "instFamily": "ETH-USDT"
                }
            ]
        }


class MockMarketAPI:
    def get_ticker(self, *args, **kwargs):
        # return last for symbol
        return {"code": "0", "data": [{"last": str(1000.0 if current_price == 0 else current_price)}]}


# -------------------- 限速器 --------------------
class RateLimiter:
    def __init__(self):
        self.last_request_time = 0.0
        self.request_count = 0
        self.window_start = time.time()
        self.max_orders_per_window = 300
        self.window_seconds = 2

    async def check_limit(self, orders_count, max_per_window=None, window_seconds=None):
        max_orders = max_per_window if max_per_window is not None else self.max_orders_per_window
        win = window_seconds if window_seconds is not None else self.window_seconds
        now = time.time()
        elapsed = now - self.window_start
        if elapsed > win:
            self.request_count = 0
            self.window_start = now
            elapsed = 0
        predicted = self.request_count + orders_count
        while predicted > max_orders:
            wait = max(0.0, win - elapsed + 0.05)
            log_action("限速器", f"等待 {wait:.2f}s 避免速率上限", "warning")
            await asyncio.sleep(wait)
            now = time.time()
            elapsed = now - self.window_start
            if elapsed > win:
                self.request_count = 0
                self.window_start = now
                break
            predicted = self.request_count + orders_count
        # small gap between requests
        if now - self.last_request_time < 0.05:
            await asyncio.sleep(max(0.0, 0.05 - (now - self.last_request_time)))
        self.request_count += orders_count
        self.last_request_time = time.time()
        log_action("限速器", f"计数: {self.request_count}/{max_orders}", "debug", {"orders": orders_count})


rate_limiter = RateLimiter()


async def check_rate_limit(n: int, max_per_window: Optional[int] = None, window_seconds: Optional[int] = None):
    await rate_limiter.check_limit(n, max_per_window=max_per_window, window_seconds=window_seconds)


# -------------------- REST：合约 / 价格 / 仓位 / 余额 --------------------
async def fetch_instrument_info_from_api() -> bool:
    """
    Fetch instrument metadata using account_api.get_instruments and update CONTRACT_INFO.
    """
    global CONTRACT_INFO, TICK_SIZE, SYMBOL, INSTRUMENTS_LOADED
    try:
        await check_rate_limit(1, max_per_window=20, window_seconds=2)
        inst_type = CONTRACT_INFO.get("instType", "SWAP")
        log_action("合约信息", f"请求合约信息 instType={inst_type} instId={CONTRACT_INFO.get('symbol')}", "debug")
        try:
            resp = await asyncio.to_thread(account_api.get_instruments, instType=inst_type, instId=CONTRACT_INFO.get("symbol"))
        except TypeError:
            resp = await asyncio.to_thread(account_api.get_instruments, inst_type, CONTRACT_INFO.get("symbol"))
        log_action("合约信息", "收到合约信息响应（原始）", "debug", resp)
        if not isinstance(resp, dict) or str(resp.get("code", "")) != "0" or not resp.get("data"):
            log_action("合约信息", "获取合约信息返回异常或 data 为空", "warning", resp)
            INSTRUMENTS_LOADED = False
            return False
        inst_list = resp.get("data", [])
        target = CONTRACT_INFO.get("symbol", "")
        found = None
        for item in inst_list:
            if item.get("instId") == target:
                found = item
                break
        if not found and target:
            base = target.split("-")[0]
            for item in inst_list:
                iid = item.get("instId", "")
                if iid.startswith(f"{base}-") and "USDT" in iid:
                    found = item
                    break
        if not found:
            log_action("合约信息", f"未找到匹配合约: {target}", "warning", {"returned_count": len(inst_list)})
            INSTRUMENTS_LOADED = False
            return False

        def _parse_float_safe(x, fallback=0.0):
            try:
                if x is None or x == "":
                    return float(fallback)
                return float(x)
            except Exception:
                return float(fallback)

        minSz = _parse_float_safe(found.get("minSz", CONTRACT_INFO.get("minSz", 0)), CONTRACT_INFO.get("minSz", 0))
        tickSz = _parse_float_safe(found.get("tickSz", CONTRACT_INFO.get("tickSz", 0)), CONTRACT_INFO.get("tickSz", 0))
        ctVal = _parse_float_safe(found.get("ctVal", CONTRACT_INFO.get("ctVal", 0)), CONTRACT_INFO.get("ctVal", 0))
        lotSz = _parse_float_safe(found.get("lotSz", CONTRACT_INFO.get("lotSz", 0)), CONTRACT_INFO.get("lotSz", 0))
        ctValCcy = found.get("ctValCcy", CONTRACT_INFO.get("ctValCcy", "ETH"))
        inst_code = found.get("instIdCode", CONTRACT_INFO.get("instIdCode"))
        inst_family = found.get("instFamily", CONTRACT_INFO.get("instFamily"))
        CONTRACT_INFO.update({
            "minSz": minSz,
            "tickSz": tickSz,
            "ctVal": ctVal,
            "lotSz": lotSz,
            "ctValCcy": ctValCcy,
            "instIdCode": inst_code,
            "instFamily": inst_family
        })
        TICK_SIZE = CONTRACT_INFO["tickSz"]
        SYMBOL = CONTRACT_INFO.get("symbol")
        INSTRUMENTS_LOADED = True
        log_action("合约信息", "已更新 CONTRACT_INFO（归一化）", "info", {
            "symbol": SYMBOL,
            "minSz": minSz,
            "tickSz": tickSz,
            "ctVal": ctVal,
            "lotSz": lotSz,
            "ctValCcy": ctValCcy,
            "instIdCode": inst_code,
            "instFamily": inst_family
        })
        return True
    except Exception as e:
        INSTRUMENTS_LOADED = False
        log_action("合约信息", f"获取合约信息异常: {e}", "error", exc_info=True)
        return False


async def update_current_price() -> bool:
    """
    Query market ticker via REST and update current_price.
    """
    global current_price, last_price, last_api_price_update, price_source
    try:
        await check_rate_limit(1)
        log_action("价格查询", "请求 ticker", "debug")
        try:
            resp = await asyncio.to_thread(market_api.get_ticker, instId=SYMBOL)
        except TypeError:
            resp = await asyncio.to_thread(market_api.get_ticker, SYMBOL)
        log_action("价格查询", "收到响应", "debug", resp)
        if isinstance(resp, dict) and str(resp.get("code", "")) in ("0", 0) and resp.get("data"):
            data0 = resp["data"][0]
            price = None
            for key in ("last", "lastPx", "price", "c", "close"):
                if key in data0:
                    price = safe_float(data0.get(key, 0), 0.0)
                    break
            if price is None:
                log_action("价格查询", "无法解析 ticker 返回中的价格字段", "warning", data0)
                return False
            last_price = current_price
            current_price = price
            last_api_price_update = time.time()
            price_source = "rest_api"
            log_action("API价格更新", f"${last_price:.4f} -> ${price:.4f}", "info")
            return True
    except Exception as e:
        log_action("价格查询", f"异常: {e}", "error", exc_info=True)
    return False


async def update_position_info() -> bool:
    """
    Query positions via REST and update position_info.
    """
    global position_info
    try:
        await check_rate_limit(1)
        log_action("仓位查询", "发送仓位查询请求", "debug")
        try:
            resp = await asyncio.to_thread(account_api.get_positions, instType=CONTRACT_INFO.get("instType", "SWAP"), instId=CONTRACT_INFO.get("symbol"))
        except TypeError:
            resp = await asyncio.to_thread(account_api.get_positions, CONTRACT_INFO.get("instType", "SWAP"), CONTRACT_INFO.get("symbol"))
        log_action("仓位查询", "收到仓位查询响应", "debug", resp)
        if not isinstance(resp, dict) or str(resp.get("code", "")) not in ("0", 0) or not resp.get("data"):
            log_action("仓位查询", "仓位查询返回非 0 或空响应", "warning", resp)
            return False
        # reset only fields; keep mapping keys
        for key in list(position_info.keys()):
            position_info[key].update({"pos": 0.0, "usdt_value": 0.0, "avg_px": 0.0, "upl": 0.0})
        data = resp.get("data", [])
        for entry in data:
            if not isinstance(entry, dict):
                continue
            inst_id = entry.get("instId") or CONTRACT_INFO.get("symbol")
            pos_raw = entry.get("pos", entry.get("position", "0"))
            pos = safe_float(pos_raw, 0.0)
            pos_side = (entry.get("posSide") or "net").lower()
            # determine logical side and absolute size
            if pos_side == "net":
                if pos < 0:
                    side = "short"
                    size = abs(pos)
                else:
                    side = "long"
                    size = pos
            elif pos_side in ("long", "short"):
                side = pos_side
                size = abs(pos)
            else:
                side = "net"
                size = pos
            # try to get markPx or last to compute notional in quote currency (USDT)
            mark_px = safe_float(entry.get("markPx") or entry.get("last") or 0.0, 0.0)
            usdt_value = 0.0
            if mark_px and CONTRACT_INFO.get("ctVal"):
                usdt_value = float(Decimal(str(size)) * Decimal(str(CONTRACT_INFO.get("ctVal", 0))) * Decimal(str(mark_px)))
            else:
                # fallback using reported notionalUsd if present
                usdt_value = safe_float(entry.get("notionalUsd", 0.0), 0.0)
            pk = f"{inst_id}-{side}"
            position_info[pk]["pos"] = size
            position_info[pk]["usdt_value"] = usdt_value
            position_info[pk]["avg_px"] = safe_float(entry.get("avgPx", 0.0))
            position_info[pk]["upl"] = safe_float(entry.get("upl", 0.0))
            position_info[pk]["entry_time"] = int(time.time())
            position_info[pk]["meta"] = {
                "posSide_raw": entry.get("posSide"),
                "posId": entry.get("posId"),
                "instType": entry.get("instType"),
                "markPx": mark_px,
                "lever": entry.get("lever")
            }
            log_action("仓位更新", f"{inst_id} {side} {size} 张 -> {usdt_value:.6f} USDT", "debug", position_info[pk])
        return True
    except Exception as e:
        log_action("仓位查询", f"请求失败: {e}", "error", exc_info=True)
        return False


async def fetch_account_balance() -> bool:
    """
    Fetch account balances and convert all currencies to USDT-equivalent.
    """
    global account_equity_usdt, initial_equity_usdt
    try:
        await check_rate_limit(1)
        log_action("账户查询", "发送账户余额请求", "debug")
        try:
            resp = await asyncio.to_thread(account_api.get_account_balance, ccy="")
        except TypeError:
            resp = await asyncio.to_thread(account_api.get_account_balance, "")
        log_action("账户查询", "收到账户余额响应", "debug", resp)
        if not isinstance(resp, dict) or str(resp.get("code", "")) not in ("0", 0) or not resp.get("data"):
            log_action("账户查询", "账户返回异常或 data 为空", "warning", resp)
            return False
        total_usdt = Decimal("0")
        balances = {}
        # data is a list: each item has 'details' list with {ccy, availEq, eq, cashBal, frozenBal, ...}
        for grp in resp.get("data", []):
            details = grp.get("details") or grp.get("details", [])
            for d in details:
                ccy = d.get("ccy") or d.get("currency") or ""
                # many API variants use 'eq' for total equity in that currency
                eq = safe_float(d.get("eq", d.get("cashBal", d.get("availEq", 0.0))), 0.0)
                balances[ccy] = eq
        # convert each currency to USDT
        for ccy, eq in balances.items():
            if ccy.upper() == "USDT":
                total_usdt += Decimal(str(eq))
                continue
            # Try to find a ticker to convert ccy -> USDT
            price = None
            candidates = [
                f"{ccy}-USDT",
                f"{ccy}-USDT-SWAP",
                f"{ccy}-USDT-SWAP".replace("--", "-"),
                f"{ccy}-USD",
                f"{ccy}-USD-SWAP"
            ]
            for cand in candidates:
                try:
                    try:
                        tresp = await asyncio.to_thread(market_api.get_ticker, instId=cand)
                    except TypeError:
                        tresp = await asyncio.to_thread(market_api.get_ticker, cand)
                    if isinstance(tresp, dict) and str(tresp.get("code", "")) in ("0", 0) and tresp.get("data"):
                        data0 = tresp["data"][0]
                        for k in ("last", "lastPx", "price", "c", "close"):
                            if k in data0:
                                price = safe_float(data0.get(k, 0), None)
                                break
                        if price is not None and price > 0:
                            log_action("余额转换", f"使用 {cand} 的价格 {price:.6f} 将 {eq} {ccy} 转换为 USDT", "debug")
                            break
                except Exception:
                    price = None
            if price is None:
                log_action("余额转换", f"无法找到 {ccy} -> USDT 的市场价格，跳过该币种的折算（视为 0）", "warning", {"ccy": ccy})
                continue
            converted = Decimal(str(eq)) * Decimal(str(price))
            total_usdt += converted
        account_equity_usdt = float(total_usdt)
        if initial_equity_usdt == 0.0:
            initial_equity_usdt = account_equity_usdt
            log_action("账户初始化", f"初始权益 (USDT): {initial_equity_usdt:.2f}", "info")
        else:
            log_action("账户更新", f"账户余额 (USDT): {account_equity_usdt:.2f}", "debug", {"balances": balances})
        return True
    except Exception as e:
        log_action("账户查询", f"异常: {e}", "error", exc_info=True)
        return False


# -------------------- 下单 / 撤单（REST） --------------------
async def place_order_simple(side: str,
                             pos_side: str,
                             ord_type: str,
                             sz: str,
                             px: Optional[str] = None,
                             td_mode: str = "isolated",
                             reduce_only: bool = False,
                             tgt_ccy: Optional[str] = None,
                             stp_mode: Optional[str] = None,
                             attach_algo_orders: Optional[list] = None,
                             cl_ord_id: Optional[str] = None) -> dict:
    """
    单笔下单封装（更严格的校验与限流）。
    """
    # 遵守单笔下单速率：60 次 / 2s
    await check_rate_limit(1, max_per_window=60, window_seconds=2)

    # 生成或使用 clOrdId
    cl = cl_ord_id or generate_order_id("ORD")

    # 处理并校验 sz（最小单位、整数倍）
    try:
        validated_sz = float(sz)
        validated_sz = validate_position_size(validated_sz)
        validated_sz = round_to_min_size(validated_sz)
        sz_str = str(validated_sz)
    except Exception:
        sz_str = str(sz)

    # 处理并校验 px（按 tickSz 四舍五入）
    if px is not None:
        try:
            pxf = float(px)
            pxf = round_price(pxf)
            px_str = str(pxf)
        except Exception:
            px_str = str(px)
    else:
        px_str = None

    req = {
        "instId": SYMBOL,
        "tdMode": td_mode,
        "clOrdId": cl,
        "side": side,
        "ordType": ord_type,
        "sz": sz_str
    }
    if pos_side:
        req["posSide"] = pos_side
    if px_str is not None:
        req["px"] = px_str
    if reduce_only:
        req["reduceOnly"] = True
    if tgt_ccy:
        req["tgtCcy"] = tgt_ccy
    if stp_mode:
        req["stpMode"] = stp_mode
    if attach_algo_orders:
        req["attachAlgoOrds"] = attach_algo_orders

    try:
        # SDK 调用放到线程池，避免阻塞事件循环
        resp = await asyncio.to_thread(trade_api.place_order, **req)
        log_action("下单", "单笔下单响应", "debug", resp)

        # 解析返回并健壮兼容大小写差异
        if not isinstance(resp, dict):
            log_action("下单", "下单返回非 dict", "warning", {"raw": resp})
            active_orders[cl] = {
                "ord_id": "",
                "cl": cl,
                "px": px_str,
                "sz": sz_str,
                "state": "unknown",
                "raw": resp,
                "create_time": time.time()
            }
            return {"code": "-1", "msg": "invalid_response", "raw": resp}

        if str(resp.get("code", "")) not in ("0", 0):
            # API 层面返回错误（如资金不足），记录并返回原始 resp
            log_action("下单", f"API 返回错误 code={resp.get('code')}", "warning", resp)
            active_orders[cl] = {
                "ord_id": "",
                "cl": cl,
                "px": px_str,
                "sz": sz_str,
                "state": "rejected",
                "raw": resp,
                "create_time": time.time()
            }
            return resp

        data0 = (resp.get("data") or [{}])[0]
        # 兼容 sCode / scode / code 等字段
        s_code = None
        for k in ("sCode", "scode", "code"):
            if k in data0:
                s_code = str(data0.get(k, ""))
                break
        ord_id = data0.get("ordId") or data0.get("ordid") or ""
        ret_cl = data0.get("clOrdId") or data0.get("clordid") or cl

        # 临时记录 active_orders（最终状态以 orders WS 推送为准）
        active_orders[ret_cl] = {
            "ord_id": ord_id,
            "cl": ret_cl,
            "px": req.get("px"),
            "sz": req.get("sz"),
            "state": "accepted" if str(s_code) in ("0", "") else "rejected",
            "raw": data0,
            "create_time": time.time()
        }
        return resp

    except Exception as e:
        log_action("下单", f"下单异常: {e}", "error", exc_info=True)
        active_orders[cl] = {
            "ord_id": "",
            "cl": cl,
            "px": px_str,
            "sz": sz_str,
            "state": "error",
            "raw": str(e),
            "create_time": time.time()
        }
        return {"code": "-1", "msg": str(e)}


async def place_multiple_orders_batch(batch: List[Dict[str, Any]], max_retry: int = 2) -> Dict[str, Any]:
    """
    批量下单封装，按订单数限流（300/2s），兼容返回字段大小写差异。
    """
    result = {"success": [], "failures": [], "raw": None}
    if not batch:
        return result

    # 限流：按订单数量计入窗口
    orders_count = len(batch)
    await check_rate_limit(orders_count, max_per_window=300, window_seconds=2)

    attempt = 0
    while attempt <= max_retry:
        attempt += 1
        try:
            resp = await asyncio.to_thread(trade_api.place_multiple_orders, batch)
            result["raw"] = resp
            if not isinstance(resp, dict):
                log_action("批量下单", f"返回非 dict（尝试 {attempt}）", "warning", resp)
                if attempt <= max_retry:
                    await asyncio.sleep(0.5 * attempt)
                    continue
                result["failures"].append({"error": "invalid_response", "resp": resp})
                return result

            if str(resp.get("code", "")) not in ("0", 0):
                log_action("批量下单", f"接口返回错误 code={resp.get('code')} (尝试 {attempt})", "error", resp)
                if attempt <= max_retry:
                    await asyncio.sleep(0.5 * attempt)
                    continue
                result["failures"].append({"error": "api_error", "resp": resp})
                return result

            data = resp.get("data", []) or []
            successes = []
            failures = []
            for item in data:
                s_code = None
                for key in ("sCode", "scode", "SCODE", "code"):
                    if key in item:
                        s_code = str(item.get(key, ""))
                        break
                cl = item.get("clOrdId") or item.get("clordid") or item.get("client_oid") or ""
                ord_id = item.get("ordId") or item.get("ordid") or ""
                if s_code is None or s_code == "":
                    s_code = str(item.get("sCode", item.get("code", "0")))
                if str(s_code) == "0":
                    successes.append({"clOrdId": cl, "ordId": ord_id, "item": item})
                else:
                    failures.append({"clOrdId": cl, "ordId": ord_id, "sCode": s_code, "item": item})

            result["success"] = successes
            result["failures"] = failures

            for s in successes:
                cl = s["clOrdId"]
                ord_id = s["ordId"]
                req = next((r for r in batch if r.get("clOrdId") == cl), None)
                px = req.get("px") if req else None
                sz = req.get("sz") if req else None
                active_orders[cl] = {"ord_id": ord_id, "cl": cl, "px": px, "sz": sz, "state": "live", "create_time": time.time()}
                log_action("批量下单", f"订单成功记录 clOrdId={cl} ordId={ord_id}", "info", {"px": px, "sz": sz})

            if failures:
                log_action("批量下单", f"检测到部分失败：{len(failures)}，尝试撤销已成功订单", "warning", {"failures": failures})
                for s in successes:
                    cl = s["clOrdId"]
                    try:
                        await asyncio.to_thread(trade_api.cancel_order, instId=batch[0].get("instId"), clOrdId=cl)
                        log_action("补偿撤单", f"已发撤单请求 clOrdId={cl}", "debug")
                    except Exception as e:
                        log_action("补偿撤单", f"撤单请求失败 clOrdId={cl} 异常: {e}", "error", exc_info=True)
                return result

            return result

        except Exception as e:
            log_action("批量下单", f"place_multiple_orders 调用异常 (尝试 {attempt}): {e}", "error", exc_info=True)
            if attempt <= max_retry:
                await asyncio.sleep(0.5 * attempt)
                continue
            result["failures"].append({"error": "exception", "msg": str(e)})
            return result

    return result


async def cancel_multiple_orders_batch(requests: List[Dict[str, Any]], max_retry: int = 1) -> Dict[str, Any]:
    """
    批量撤单封装，按订单数限流（300/2s）。
    """
    ret = {"accepted": [], "rejected": [], "raw": None}
    if not requests:
        return ret

    orders_count = len(requests)
    await check_rate_limit(orders_count, max_per_window=300, window_seconds=2)

    attempt = 0
    while attempt <= max_retry:
        attempt += 1
        try:
            resp = await asyncio.to_thread(trade_api.cancel_multiple_orders, requests)
            ret["raw"] = resp
            if not isinstance(resp, dict):
                log_action("批量撤单", f"返回非 dict (尝试 {attempt})", "warning", resp)
                if attempt <= max_retry:
                    await asyncio.sleep(0.3 * attempt)
                    continue
                ret["rejected"].append({"error": "invalid_response", "resp": resp})
                return ret

            if str(resp.get("code", "")) not in ("0", 0):
                log_action("批量撤单", f"接口返回错误 code={resp.get('code')} (尝试 {attempt})", "error", resp)
                if attempt <= max_retry:
                    await asyncio.sleep(0.3 * attempt)
                    continue
                ret["rejected"].append({"error": "api_error", "resp": resp})
                return ret

            data = resp.get("data", []) or []
            for item in data:
                s_code = None
                for key in ("sCode", "scode", "SCODE", "code"):
                    if key in item:
                        s_code = str(item.get(key, ""))
                        break
                if s_code is None or s_code == "":
                    s_code = str(item.get("sCode", item.get("code", "0")))

                cl = item.get("clOrdId") or item.get("clordid") or ""
                ord_id = item.get("ordId") or item.get("ordid") or ""

                if str(s_code) == "0":
                    ret["accepted"].append({"clOrdId": cl, "ordId": ord_id, "item": item})
                    if cl and cl in active_orders:
                        active_orders[cl]["state"] = "cancel_pending"
                else:
                    ret["rejected"].append({"clOrdId": cl, "ordId": ord_id, "sCode": s_code, "item": item})

            return ret

        except Exception as e:
            log_action("批量撤单", f"cancel_multiple_orders 调用异常 (尝试 {attempt}): {e}", "error", exc_info=True)
            if attempt <= max_retry:
                await asyncio.sleep(0.3 * attempt)
                continue
            ret["rejected"].append({"error": "exception", "msg": str(e)})
            return ret

    return ret


# -------------------- 订单查询（REST） --------------------
async def get_order_info(ordId: str = None, clOrdId: str = None, instId: str = None) -> dict:
    """
    使用 REST 查询单笔订单信息（get_order），并更新 active_orders。
    """
    if instId is None:
        instId = SYMBOL
    await check_rate_limit(1, max_per_window=60, window_seconds=2)
    try:
        resp = await asyncio.to_thread(trade_api.get_order, instId=instId, ordId=ordId, clOrdId=clOrdId)
    except TypeError:
        try:
            resp = await asyncio.to_thread(trade_api.get_order, instId, ordId or "", clOrdId or "")
        except Exception as e:
            log_action("查询订单", f"调用 SDK get_order 异常: {e}", "error", exc_info=True)
            return {"code": "-1", "msg": str(e)}

    log_action("查询订单", "get_order 返回（原始）", "debug", resp)

    try:
        if not isinstance(resp, dict) or str(resp.get("code", "")) not in ("0", 0) or not resp.get("data"):
            return resp
        entry = resp["data"][0]
        ord_id = entry.get("ordId") or entry.get("ordid") or ""
        cl = entry.get("clOrdId") or entry.get("clordid") or ""
        state = entry.get("state") or ""
        acc_fill_sz = safe_float(entry.get("accFillSz", entry.get("acc_fill_sz", 0)), 0.0)
        fill_sz = safe_float(entry.get("fillSz", entry.get("fill_sz", 0)), 0.0)
        avg_px = safe_float(entry.get("avgPx", entry.get("avg_px", 0)), 0.0)
        px = entry.get("px", "")
        sz = entry.get("sz", "")
        u_time = entry.get("uTime") or entry.get("u_time") or ""

        updated = False
        if cl:
            ao = active_orders.get(cl, {})
            ao.update({
                "ord_id": ord_id,
                "cl": cl,
                "state": state,
                "accFillSz": acc_fill_sz,
                "fillSz": fill_sz,
                "avgPx": avg_px,
                "px": px,
                "sz": sz,
                "uTime": u_time,
                "raw_order": entry
            })
            active_orders[cl] = ao
            updated = True
        else:
            for k, v in list(active_orders.items()):
                if v.get("ord_id") and str(v.get("ord_id")) == str(ord_id):
                    v.update({
                        "ord_id": ord_id,
                        "cl": v.get("cl", ""),
                        "state": state,
                        "accFillSz": acc_fill_sz,
                        "fillSz": fill_sz,
                        "avgPx": avg_px,
                        "px": px,
                        "sz": sz,
                        "uTime": u_time,
                        "raw_order": entry
                    })
                    active_orders[k] = v
                    updated = True
                    break
        if not updated:
            key = cl or ord_id or generate_order_id("ORDINFO")
            active_orders[key] = {
                "ord_id": ord_id,
                "cl": cl,
                "state": state,
                "accFillSz": acc_fill_sz,
                "fillSz": fill_sz,
                "avgPx": avg_px,
                "px": px,
                "sz": sz,
                "uTime": u_time,
                "raw_order": entry
            }
        return resp
    except Exception as e:
        log_action("查询订单", f"解析 get_order 返回异常: {e}", "error", exc_info=True)
        return resp


async def get_pending_orders(instType: str = None, instId: str = None, limit: int = 100) -> dict:
    """
    查询未成交订单列表（orders-pending），并更新 active_orders。
    """
    await check_rate_limit(1, max_per_window=60, window_seconds=2)
    try:
        params = {}
        if instType:
            params["instType"] = instType
        if instId:
            params["instId"] = instId
        if limit:
            params["limit"] = str(limit)
        try:
            resp = await asyncio.to_thread(trade_api.get_order_list, **params)
        except TypeError:
            try:
                resp = await asyncio.to_thread(trade_api.get_order_list, params.get("instType", ""), params.get("ordType", ""))
            except Exception as e:
                log_action("查询未成交订单", f"调用 SDK get_order_list 异常: {e}", "error", exc_info=True)
                return {"code": "-1", "msg": str(e)}
        log_action("查询未成交订单", "get_order_list 返回（原始）", "debug", resp)
        if not isinstance(resp, dict) or str(resp.get("code", "")) not in ("0", 0) or not resp.get("data"):
            return resp
        data = resp.get("data", []) or []
        for entry in data:
            try:
                ord_id = entry.get("ordId") or entry.get("ordid") or ""
                cl = entry.get("clOrdId") or entry.get("clordid") or ""
                state = entry.get("state") or ""
                px = entry.get("px", "")
                sz = entry.get("sz", "")
                avg_px = safe_float(entry.get("avgPx", 0), 0.0)
                acc_fill_sz = safe_float(entry.get("accFillSz", 0), 0.0)
                key = cl or ord_id or generate_order_id("PENDING")
                active_orders[key] = {
                    "ord_id": ord_id,
                    "cl": cl,
                    "state": state,
                    "px": px,
                    "sz": sz,
                    "avgPx": avg_px,
                    "accFillSz": acc_fill_sz,
                    "raw_order": entry,
                    "last_update": time.time()
                }
            except Exception:
                log_action("查询未成交订单", "解析单条未成交订单异常", "warning", entry)
        return resp
    except Exception as e:
        log_action("查询未成交订单", f"异常: {e}", "error", exc_info=True)
        return {"code": "-1", "msg": str(e)}


async def confirm_order_final_state(ordId: str = None, clOrdId: str = None, timeout: float = 5.0) -> dict:
    """
    快速确认订单最终状态（REST辅助）。
    """
    resp = await get_order_info(ordId=ordId, clOrdId=clOrdId)
    return resp


# -------------------- WebSocket：持仓 / 余额 / 订单 / 成交 / 公共行情 --------------------
def _handle_positions_ws_entry(entry: Dict[str, Any]):
    try:
        inst_id = entry.get("instId")
        pos_raw = entry.get("pos", "0")
        pos = safe_float(pos_raw, 0.0)
        pos_side = (entry.get("posSide") or "net").lower()
        if pos_side == "net":
            if pos < 0:
                side = "short"
                size = abs(pos)
            else:
                side = "long"
                size = pos
        elif pos_side in ("long", "short"):
            side = pos_side
            size = abs(pos)
        else:
            side = "net"
            size = pos
        mark_px = safe_float(entry.get("markPx") or entry.get("last") or 0.0, 0.0)
        usdt_value = 0.0
        if mark_px and CONTRACT_INFO.get("ctVal"):
            usdt_value = float(Decimal(str(size)) * Decimal(str(CONTRACT_INFO.get("ctVal", 0))) * Decimal(str(mark_px)))
        else:
            usdt_value = safe_float(entry.get("notionalUsd", 0.0), 0.0)
        pk = f"{inst_id}-{side}"
        position_info[pk]["pos"] = size
        position_info[pk]["usdt_value"] = usdt_value
        position_info[pk]["avg_px"] = safe_float(entry.get("avgPx", 0.0))
        position_info[pk]["upl"] = safe_float(entry.get("upl", 0.0))
        position_info[pk]["entry_time"] = int(time.time())
        log_action("WS仓位", f"{inst_id} {side} {size} -> {usdt_value:.6f}USDT", "debug", position_info[pk])
    except Exception as e:
        log_action("WS仓位处理", f"错误: {e}", "error", exc_info=True)


def _handle_balance_and_position_ws_entry(entry: Dict[str, Any]):
    global account_equity_usdt, initial_equity_usdt, last_ws_price_update
    try:
        bal_data = entry.get("balData", []) or entry.get("bal", [])
        if isinstance(bal_data, dict):
            bal_data = [bal_data]
        total_usdt = Decimal("0")
        for b in bal_data:
            ccy = b.get("ccy")
            eq = safe_float(b.get("cashBal", b.get("eq", 0.0)), 0.0)
            if ccy and ccy.upper() == "USDT":
                total_usdt += Decimal(str(eq))
            else:
                price = None
                try:
                    tresp = None
                    try:
                        tresp = market_api.get_ticker(instId=f"{ccy}-USDT")
                    except Exception:
                        try:
                            tresp = market_api.get_ticker(f"{ccy}-USDT")
                        except Exception:
                            tresp = None
                    if isinstance(tresp, dict) and tresp.get("data"):
                        data0 = tresp["data"][0]
                        for k in ("last", "lastPx", "price", "c", "close"):
                            if k in data0:
                                price = safe_float(data0.get(k, 0.0), 0.0)
                                break
                except Exception:
                    price = None
                if price and price > 0:
                    total_usdt += Decimal(str(eq)) * Decimal(str(price))
                else:
                    log_action("WS余额转换", f"无法在 WS 回调中转换 {ccy} -> USDT（视为 0）", "warning", {"ccy": ccy})
        account_equity_usdt = float(total_usdt)
        if initial_equity_usdt == 0.0:
            initial_equity_usdt = account_equity_usdt
        last_ws_price_update = time.time()
        log_action("WS余额更新", f"账户余额 (USDT): {account_equity_usdt:.2f}", "debug")
    except Exception as e:
        log_action("WS balance处理", f"异常: {e}", "error", exc_info=True)


def _handle_order_ws_entry(entry: dict):
    try:
        ord_id = entry.get("ordId") or entry.get("ordid") or ""
        cl = entry.get("clOrdId") or entry.get("clordid") or ""
        trade_id = entry.get("tradeId") or entry.get("trade_id") or ""
        state = entry.get("state") or ""
        req_id = entry.get("reqId") or entry.get("req_id") or ""
        u_time = entry.get("uTime") or entry.get("u_time") or ""
        fill_sz = safe_float(entry.get("fillSz", entry.get("fill_sz", 0)), 0.0)
        acc_fill_sz = safe_float(entry.get("accFillSz", entry.get("acc_fill_sz", 0)), 0.0)
        fill_px = safe_float(entry.get("fillPx", entry.get("fill_px", 0)), 0.0)
        avg_px = safe_float(entry.get("avgPx", entry.get("avg_px", 0)), 0.0)

        if req_id:
            if req_id in seen_reqids:
                log_action("WS订单", f"重复 reqId 推送，忽略 reqId={req_id}", "debug")
                return
            seen_reqids.add(req_id)

        if trade_id:
            if trade_id in seen_trade_ids:
                log_action("WS订单", f"重复 tradeId 推送，忽略 tradeId={trade_id}", "debug")
                return
            seen_trade_ids.add(trade_id)

        if not trade_id and state == "filled" and ord_id:
            if ord_id in seen_filled_ordids:
                log_action("WS订单", f"重复 filled 推送，忽略 ordId={ord_id}", "debug")
                return
            seen_filled_ordids.add(ord_id)

        key = cl or ord_id or generate_order_id("ORDWS")
        ao = active_orders.get(key, {})
        ao.update({
            "ord_id": ord_id,
            "cl": cl,
            "state": state,
            "fillSz": fill_sz,
            "accFillSz": acc_fill_sz,
            "fillPx": fill_px,
            "avgPx": avg_px,
            "tradeId": trade_id,
            "execType": entry.get("execType") or entry.get("exec_type"),
            "px": entry.get("px"),
            "sz": entry.get("sz"),
            "tdMode": entry.get("tdMode"),
            "uTime": u_time,
            "raw_ws": entry,
            "last_update": time.time()
        })
        active_orders[key] = ao

        log_action("WS订单更新", f"更新订单 {key} state={state} fillSz={fill_sz} accFillSz={acc_fill_sz}", "info", {"ord": ord_id, "cl": cl, "tradeId": trade_id})

    except Exception as e:
        log_action("WS订单处理", f"异常: {e}", "error", exc_info=True)


def _handle_fills_ws_entry(entry: dict):
    try:
        trade_id = entry.get("tradeId") or entry.get("trade_id") or ""
        if not trade_id:
            return
        if trade_id in seen_trade_ids:
            log_action("WS成交", f"重复 tradeId 推送（fills），忽略 tradeId={trade_id}", "debug")
            return
        seen_trade_ids.add(trade_id)

        ord_id = entry.get("ordId") or entry.get("ordid") or ""
        cl = entry.get("clOrdId") or entry.get("clordid") or ""
        fill_sz = safe_float(entry.get("fillSz", 0), 0.0)
        fill_px = safe_float(entry.get("fillPx", 0), 0.0)
        ts = entry.get("ts") or entry.get("time") or ""
        exec_type = entry.get("execType") or entry.get("exec_type")

        key = cl or ord_id
        if key and key in active_orders:
            ao = active_orders[key]
            ao["tradeId"] = trade_id
            ao["fillSz"] = fill_sz
            ao["fillPx"] = fill_px
            ao["execType"] = exec_type
            ao["last_fill_ts"] = ts
            ao["last_update"] = time.time()
            if entry.get("state") == "filled" or entry.get("accFillSz"):
                ao["state"] = entry.get("state", ao.get("state"))
            active_orders[key] = ao
            log_action("WS成交更新", f"填充订单 {key} tradeId={trade_id} fillSz={fill_sz} fillPx={fill_px}", "info", {"ord": ord_id, "cl": cl})
        else:
            k2 = key or ord_id or generate_order_id("FILL")
            active_orders[k2] = {
                "ord_id": ord_id,
                "cl": cl,
                "tradeId": trade_id,
                "fillSz": fill_sz,
                "fillPx": fill_px,
                "last_fill_ts": ts,
                "last_update": time.time(),
                "raw_fill": entry
            }
            log_action("WS成交新建", f"新增成交记录 {k2} tradeId={trade_id}", "debug", entry)

    except Exception as e:
        log_action("WS成交处理", f"异常: {e}", "error", exc_info=True)


# 处理 WS op 下单 / 批量下单 的直接响应（op="order" / "batch-orders"）
def _handle_ws_order_op_response(ws_message: dict):
    try:
        op = ws_message.get("op")
        code = str(ws_message.get("code", ""))
        data = ws_message.get("data", []) or []
        if isinstance(data, dict):
            data = [data]
        log_action("WS下单响应", f"op={op} code={code}", "debug", ws_message)
        for item in data:
            cl = item.get("clOrdId") or item.get("clordid") or ""
            ord_id = item.get("ordId") or item.get("ordid") or ""
            s_code = None
            for k in ("sCode", "scode", "SCODE", "code"):
                if k in item:
                    s_code = str(item.get(k, ""))
                    break
            s_msg = item.get("sMsg") or item.get("smsg") or ""
            key = cl or ord_id or generate_order_id("WSORD")
            ao = active_orders.get(key, {})
            ao.update({
                "ord_id": ord_id,
                "cl": cl,
                "ws_op": op,
                "sCode": s_code,
                "sMsg": s_msg,
                "raw_ws_order_resp": item,
                "last_update": time.time()
            })
            if s_code in ("0", "", None):
                ao["state"] = "accepted"
            else:
                ao["state"] = "rejected"
            active_orders[key] = ao
            log_action("WS下单响应处理", f"记录订单 {key} sCode={s_code} ordId={ord_id}", "info", ao)
    except Exception as e:
        log_action("WS下单响应处理", f"异常: {e}", "error", exc_info=True)


# 处理 WS 撤单 / 批量撤单 的直接响应（op="cancel-order" / "batch-cancel-orders"）
def _handle_ws_cancel_op_response(ws_message: dict):
    try:
        op = ws_message.get("op")
        code = str(ws_message.get("code", ""))
        data = ws_message.get("data", []) or []
        if isinstance(data, dict):
            data = [data]
        log_action("WS撤单响应", f"接收 op={op} code={code}", "debug", ws_message)
        for item in data:
            cl = item.get("clOrdId") or item.get("clordid") or ""
            ord_id = item.get("ordId") or item.get("ordid") or ""
            s_code = None
            for k in ("sCode", "scode", "SCODE", "code"):
                if k in item:
                    s_code = str(item.get(k, ""))
                    break
            s_msg = item.get("sMsg") or item.get("smsg") or ""
            key = cl or ord_id or generate_order_id("WSCANCEL")
            ao = active_orders.get(key, {})
            ao.update({
                "ord_id": ord_id,
                "cl": cl,
                "ws_cancel_op": op,
                "ws_cancel_sCode": s_code,
                "ws_cancel_sMsg": s_msg,
                "raw_ws_cancel_resp": item,
                "last_update": time.time()
            })
            if s_code in ("0", "", None):
                ao["state"] = "cancel_pending"
                log_action("WS撤单处理", f"撤单请求已被接受，标记 cancel_pending key={key} ordId={ord_id}", "info", ao)
            else:
                ao["state"] = "cancel_rejected"
                ao["cancel_reject_reason"] = s_msg
                log_action("WS撤单处理", f"撤单被拒 key={key} ordId={ord_id} sCode={s_code} sMsg={s_msg}", "warning", ao)
            active_orders[key] = ao
    except Exception as e:
        log_action("WS撤单响应处理", f"异常: {e}", "error", exc_info=True)


def _ws_message_callback_enhanced(message: Any):
    """
    WS 私有频道通用回调，分发到 positions / balance_and_position / orders / fills / op(order/cancel)
    """
    try:
        data = message
        if isinstance(message, str):
            try:
                data = json.loads(message)
            except Exception:
                log_action("WS消息", "收到非 JSON 字符串消息", "debug", {"raw": message})
                return
        if "event" in data:
            ev = data.get("event")
            log_action("WS事件", f"event={ev}", "debug", data.get("arg"))
            return

        # 先处理 op-level 的下单/撤单响应
        if "op" in data and data.get("op") in ("order", "batch-orders", "cancel-order", "batch-cancel-orders"):
            opv = data.get("op")
            if opv in ("order", "batch-orders"):
                _handle_ws_order_op_response(data)
            else:
                _handle_ws_cancel_op_response(data)
            return

        arg = data.get("arg") or {}
        channel = arg.get("channel") or data.get("channel")
        if channel == "orders":
            payload_list = data.get("data", [])
            if isinstance(payload_list, dict):
                payload_list = [payload_list]
            for payload in payload_list:
                if isinstance(payload, list):
                    for it in payload:
                        _handle_order_ws_entry(it)
                else:
                    _handle_order_ws_entry(payload)
            return
        if channel == "fills":
            payload_list = data.get("data", [])
            if isinstance(payload_list, dict):
                payload_list = [payload_list]
            for payload in payload_list:
                _handle_fills_ws_entry(payload)
            return
        if channel in ("positions", "balance_and_position"):
            payload_list = data.get("data", [])
            if isinstance(payload_list, dict):
                payload_list = [payload_list]
            for payload in payload_list:
                if channel == "positions":
                    _handle_positions_ws_entry(payload)
                else:
                    _handle_balance_and_position_ws_entry(payload)
            return

        log_action("WS消息", f"未知频道: {channel}", "debug", data)
    except Exception as e:
        log_action("WS回调", f"处理消息异常: {e}", "error", exc_info=True)


async def start_private_ws_enhanced():
    """
    启动私有 WS，订阅 positions, balance_and_position, orders, 可选 fills。
    """
    global _ws_instance
    if PrivateWs is None:
        log_action("WS", "WsPrivateAsync 不可用（SDK 未安装），跳过 WS 订阅", "warning")
        return None
    try:
        ws = PrivateWs(apiKey=API_KEY, passphrase=PASSPHRASE, secretKey=SECRET_KEY, url="wss://ws.okx.com:8443/ws/v5/private", useServerTime=False)
        await ws.start()
        _ws_instance = ws
        log_action("WS", "私有 WS 已启动", "info")
        args = [
            {"channel": "positions", "instType": "ANY"},
            {"channel": "balance_and_position"},
            {"channel": "orders", "instType": "ANY"}
        ]
        if ENABLE_FILLS_CHANNEL:
            args.append({"channel": "fills"})
        await ws.subscribe(args, callback=_ws_message_callback_enhanced)
        log_action("WS", "已订阅: " + ", ".join(a.get("channel") for a in args), "info", {"sub_args": args})
        try:
            asyncio.create_task(get_pending_orders(instType=CONTRACT_INFO.get("instType", "SWAP"), instId=SYMBOL, limit=100))
        except Exception:
            pass
        return ws
    except Exception as e:
        log_action("WS启动", f"启动或订阅失败: {e}", "error", exc_info=True)
        return None


async def stop_private_ws():
    global _ws_instance
    try:
        if _ws_instance is None:
            return
        try:
            await _ws_instance.stop()
        except Exception:
            pass
        _ws_instance = None
        log_action("WS", "私有 WS 已停止", "info")
    except Exception as e:
        log_action("WS停止", f"停止失败: {e}", "warning", exc_info=True)


# -------------------- 通过 WS 发送下单 / 批量下单 / 撤单 的辅助（可选用） --------------------
async def ws_send_order(ws, order_args: dict, msg_id: str = None):
    if msg_id is None:
        msg_id = generate_order_id("WSORD")
    await check_rate_limit(1, max_per_window=60, window_seconds=2)
    payload = {"id": msg_id, "op": "order", "args": [order_args]}
    try:
        if hasattr(ws, "request"):
            await ws.request(payload)
        elif hasattr(ws, "send"):
            await ws.send(json.dumps(payload))
        else:
            await asyncio.to_thread(ws.send, json.dumps(payload))
        log_action("WS下单发送", f"已发送 WS order id={msg_id}", "debug", payload)
    except Exception as inner:
        log_action("WS下单发送", f"发送失败: {inner}", "error", exc_info=True)


async def ws_send_batch_orders(ws, orders: list, msg_id: str = None):
    if msg_id is None:
        msg_id = generate_order_id("WSBATCH")
    await check_rate_limit(len(orders), max_per_window=300, window_seconds=2)
    payload = {"id": msg_id, "op": "batch-orders", "args": orders}
    try:
        if hasattr(ws, "request"):
            await ws.request(payload)
        elif hasattr(ws, "send"):
            await ws.send(json.dumps(payload))
        else:
            await asyncio.to_thread(ws.send, json.dumps(payload))
        log_action("WS批量下单发送", f"已发送 WS batch-orders id={msg_id} orders={len(orders)}", "debug")
    except Exception as e:
        log_action("WS批量下单发送", f"发送异常: {e}", "error", exc_info=True)


async def ws_send_cancel_order(ws, instId: str, ordId: str = None, clOrdId: str = None, msg_id: str = None):
    if msg_id is None:
        msg_id = generate_order_id("WSCXL")
    await check_rate_limit(1, max_per_window=60, window_seconds=2)
    payload = {"id": msg_id, "op": "cancel-order", "args": [{"instId": instId, "ordId": ordId or "", "clOrdId": clOrdId or ""}]}
    try:
        if hasattr(ws, "request"):
            await ws.request(payload)
        elif hasattr(ws, "send"):
            await ws.send(json.dumps(payload))
        else:
            await asyncio.to_thread(ws.send, json.dumps(payload))
        log_action("WS撤单发送", f"已发送 WS cancel-order id={msg_id} instId={instId} ordId={ordId} cl={clOrdId}", "debug", payload)
    except Exception as e:
        log_action("WS撤单发送", f"发送异常: {e}", "error", exc_info=True)


async def ws_send_batch_cancel_orders(ws, requests: list, msg_id: str = None):
    if msg_id is None:
        msg_id = generate_order_id("WSBATCHCXL")
    orders_count = len(requests)
    await check_rate_limit(orders_count, max_per_window=300, window_seconds=2)
    payload = {"id": msg_id, "op": "batch-cancel-orders", "args": requests}
    try:
        if hasattr(ws, "request"):
            await ws.request(payload)
        elif hasattr(ws, "send"):
            await ws.send(json.dumps(payload))
        else:
            await asyncio.to_thread(ws.send, json.dumps(payload))
        log_action("WS批量撤单发送", f"已发送 WS batch-cancel-orders id={msg_id} count={orders_count}", "debug")
    except Exception as e:
        log_action("WS批量撤单发送", f"发送异常: {e}", "error", exc_info=True)


# -------------------- 公共行情 WS（tickers） --------------------
def _public_ws_ticker_callback(message: Any):
    global current_price, last_price, last_ws_price_update, price_source, best_bid, best_ask
    try:
        data = message
        if isinstance(message, str):
            try:
                data = json.loads(message)
            except Exception:
                log_action("Public WS", "收到非 JSON 字符串消息（tickers）", "debug", {"raw": message})
                return

        if "event" in data:
            ev = data.get("event")
            log_action("Public WS 事件", f"event={ev}", "debug", data.get("arg"))
            return

        arg = data.get("arg") or {}
        channel = arg.get("channel") or data.get("channel")
        if channel != "tickers":
            return

        payload_list = data.get("data", []) or []
        if isinstance(payload_list, dict):
            payload_list = [payload_list]
        for payload in payload_list:
            price = None
            for k in ("last", "lastPx", "price", "c", "close"):
                if k in payload:
                    price = safe_float(payload.get(k), None)
                    break
            if price is None:
                bid = safe_float(payload.get("bidPx", 0), 0.0)
                ask = safe_float(payload.get("askPx", 0), 0.0)
                if bid and ask:
                    price = (bid + ask) / 2.0
                elif bid:
                    price = bid
                elif ask:
                    price = ask

            if price is None:
                log_action("Public WS tickers", "无法解析价格字段", "warning", payload)
                continue

            best_bid = safe_float(payload.get("bidPx", best_bid), best_bid)
            best_ask = safe_float(payload.get("askPx", best_ask), best_ask)

            last_price = current_price
            current_price = float(price)
            last_ws_price_update = time.time()
            price_source = "ws_ticker"

            try:
                if last_price == 0 or abs(current_price - last_price) / max(1.0, last_price) > 0.0005:
                    log_action("行情更新", f"WS tickers 价格更新: {last_price:.6f} -> {current_price:.6f}", "info",
                               {"instId": arg.get("instId"), "bid": best_bid, "ask": best_ask, "ts": payload.get("ts")})
                else:
                    log_action("行情更新", "WS tickers 微幅变动（debug）", "debug", {"last": last_price, "now": current_price})
            except Exception:
                log_action("行情更新", "记录行情更新日志时异常", "debug", payload)

    except Exception as e:
        log_action("Public WS tickers 处理", f"异常: {e}", "error", exc_info=True)


async def start_public_ws():
    global _public_ws_instance
    if not ENABLE_PUBLIC_TICKER:
        log_action("Public WS", "ENABLE_PUBLIC_TICKER=False，跳过公共行情订阅", "info")
        return None
    if PublicWs is None:
        log_action("Public WS", "WsPublicAsync 未安装，无法订阅 tickers（跳过）", "warning")
        return None
    try:
        ws = PublicWs(url="wss://wspap.okx.com:8443/ws/v5/public")
        await ws.start()
        _public_ws_instance = ws
        log_action("Public WS", "公共 WS 已启动", "info")
        args = [{"channel": "tickers", "instId": SYMBOL}]
        await ws.subscribe(args, callback=_public_ws_ticker_callback)
        log_action("Public WS", "已订阅 tickers", "info", {"sub_args": args})
        return ws
    except Exception as e:
        log_action("Public WS 启动", f"启动或订阅失败: {e}", "error", exc_info=True)
        return None


async def stop_public_ws():
    global _public_ws_instance
    try:
        if _public_ws_instance is None:
            return
        try:
            await _public_ws_instance.stop()
        except Exception:
            pass
        _public_ws_instance = None
        log_action("Public WS", "公共 WS 已停止", "info")
    except Exception as e:
        log_action("Public WS 停止", f"停止失败: {e}", "warning", exc_info=True)


# -------------------- 主循环与监控 --------------------
def log_periodic_status():
    long_key = f"{CONTRACT_INFO.get('symbol')}-long"
    short_key = f"{CONTRACT_INFO.get('symbol')}-short"
    long_pos = position_info[long_key]["pos"] if long_key in position_info else 0.0
    short_pos = position_info[short_key]["pos"] if short_key in position_info else 0.0
    logger.info("\n" + "=" * 80)
    logger.info(f"📊 状态 - 方向: {trading_direction} - 多: {long_pos} - 空: {short_pos} - 余额(USDT): {account_equity_usdt:.2f}")
    logger.info("=" * 80 + "\n")


async def main_loop_once():
    if not INSTRUMENTS_LOADED:
        ok = await fetch_instrument_info_from_api()
        if not ok:
            log_action("主流程", "未能加载合约元数据，进入 Dry-run 模式（不会下单）", "warning")
            await update_current_price()
            await fetch_account_balance()
            await update_position_info()
            log_periodic_status()
            return
    await update_current_price()
    await fetch_account_balance()
    await update_position_info()
    if not active_orders:
        log_action("主流程", "无活跃订单（或仅观测模式），当前不会主动下单（策略留空）", "info")
    log_periodic_status()


async def main_loop_continuous():
    # 启动私有 WS 与公共 WS（如果启用）
    ws_task = None
    public_task = None
    if not USE_MOCK and PrivateWs is not None:
        ws_task = asyncio.create_task(start_private_ws_enhanced())
    if not USE_MOCK and PublicWs is not None and ENABLE_PUBLIC_TICKER:
        public_task = asyncio.create_task(start_public_ws())
    try:
        while True:
            try:
                await main_loop_once()
            except Exception as e:
                log_action("主循环", f"异常: {e}", "error", exc_info=True)
            await asyncio.sleep(5)
    finally:
        if ws_task:
            try:
                await stop_private_ws()
            except Exception:
                pass
        if public_task:
            try:
                await stop_public_ws()
            except Exception:
                pass


# -------------------- 客户端初始化 --------------------
def initialize_clients():
    global account_api, trade_api, market_api
    if USE_MOCK:
        account_api = MockAccountAPI()
        trade_api = MockTradeAPI()
        market_api = MockMarketAPI()
        log_action("初始化", "使用 Mock APIs (USE_MOCK=1)", "info")
    else:
        if Account is None or Trade is None or MarketData is None:
            log_action("初始化", "OKX SDK 未安装且 USE_MOCK=False，无法继续", "error")
            raise RuntimeError("OKX SDK not installed; set USE_MOCK=1 to run mock mode")
        account_api = Account.AccountAPI(API_KEY, SECRET_KEY, PASSPHRASE, False, OKX_FLAG)
        trade_api = Trade.TradeAPI(API_KEY, SECRET_KEY, PASSPHRASE, False, OKX_FLAG)
        market_api = MarketData.MarketAPI(API_KEY, SECRET_KEY, PASSPHRASE, False, OKX_FLAG)
        log_action("初始化", f"已初始化 OKX SDK (flag={OKX_FLAG})", "info")


# -------------------- 程序入口 --------------------
if __name__ == "__main__":
    initialize_clients()
    log_action("程序启动", f"模式: OKX_FLAG={OKX_FLAG}, USE_MOCK={USE_MOCK}", "info")
    if RUN_FOREVER:
        asyncio.run(main_loop_continuous())
    else:
        asyncio.run(main_loop_once())
