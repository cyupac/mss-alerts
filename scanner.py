#!/usr/bin/env python3
"""
MSS ICT Telegram scanner
========================
Runs for free on GitHub Actions every 5 minutes. It downloads candles from
Twelve Data, finds the same setups as the MSS indicator (4H/1H trend, CHoCH,
key-level liquidity sweep, CISD, FVG / order block retest) and sends the
alerts to your phone with the free ntfy app (or Telegram). Your computer can
be switched off.

Only Python's built-in libraries are used, so nothing needs installing.

  python scanner.py scan   -> normal run (used by the schedule)
  python scanner.py test   -> sends a status message for every symbol now
"""

import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from bisect import bisect_right
from datetime import date, datetime, timedelta, timezone

# =====================================================================
#  SETTINGS - change these on GitHub (pencil icon) whenever you like
# =====================================================================

# Twelve Data symbols. With the free plan keep it to 2 symbols at most
# (each symbol costs 1 credit per run, the free plan gives 800 a day).
# Examples: "XAU/USD", "GBP/USD", "EUR/USD", "BTC/USD"
SYMBOLS = ["XAU/USD", "GBP/USD", "BTC/USD"]

# Chart timeframe the scanner works on: "15min" (recommended) or "5min"
TIMEFRAME = "1min"

# Which setups to send: "A+" = A+ only, "A" = A+ and A, "B" = all
QUALITY = "B"

# Your money (used for the lot size in the entry message)
ACCOUNT_SIZE = 5000.0      # in USD
RISK_PCT = 1.0              # % of the account you lose if the stop is hit

# Targets and trade management
RR1 = 2.0                   # target 1 in R
RR2 = 3.0                   # target 2 in R
PARTIAL_PCT = 50.0          # % closed at target 1
BREAK_EVEN = True           # move stop to entry after target 1
MAX_PER_DAY = 3             # max trades per day (0 = no limit)
DAY_STOP_R = 3.0            # stop for the day after losing this many R (0 = off)

# Which messages you get
ALERT_CHOCH = True          # graded CHoCH: get ready
ALERT_ENTRY = True          # BUY / SELL entry with stop, targets, lot size
ALERT_RESULT = True         # target 1 hit, trade closed
ALERT_SIGNS = True         # key-level sweep and CISD (more messages)

# Filters
USE_ROOM = True             # skip a trade when a key level blocks target 1
USE_CHOP = True             # skip trades when the market is choppy
CHOP_BARS = 60
CHOP_MAX = 4
KZ_ONLY = False             # only enter during London and New York
SIGN_TREND = True           # sweeps / CISD only when they fit the 4H/1H trend

# Sessions in New York time (start hour, end hour)
ASIA = (19, 2)
LONDON = (2, 6)
NEW_YORK = (7, 11)

# Messages about candles that closed longer ago than this are marked late,
# and anything older than MAX_AGE_MINUTES is not sent at all.
LATE_MINUTES = 30
MAX_AGE_MINUTES = 180

# Advanced (no need to change)
DISP_MULT = 1.2
MIN_FVG = 0.15
MAX_WAIT = 40
SL_BUF = 0.15
MAX_STOP = 5.0
HTF_LEN = 3
PD_LEN = 24
CISD_WAIT = 20
ATR_LEN = 14

# =====================================================================

STATE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "state.json")
UTC = timezone.utc


class Bar:
    __slots__ = ("t", "o", "h", "l", "c")

    def __init__(self, t, o, h, l, c):
        self.t, self.o, self.h, self.l, self.c = t, o, h, l, c


# ----------------------------- time helpers -----------------------------

def _nth_sunday(year, month, n):
    d = date(year, month, 1)
    d += timedelta(days=(6 - d.weekday()) % 7)
    return d + timedelta(days=7 * (n - 1))


def ny_offset(utc_dt):
    """New York offset from UTC (daylight saving included)."""
    y = utc_dt.year
    start = datetime.combine(_nth_sunday(y, 3, 2), datetime.min.time(), UTC) + timedelta(hours=7)
    end = datetime.combine(_nth_sunday(y, 11, 1), datetime.min.time(), UTC) + timedelta(hours=6)
    return timedelta(hours=-4) if start <= utc_dt < end else timedelta(hours=-5)


def to_ny(utc_dt):
    return (utc_dt + ny_offset(utc_dt)).replace(tzinfo=None)


def trading_date(utc_dt):
    """Forex day: it starts at 17:00 New York time."""
    return (to_ny(utc_dt) + timedelta(hours=7)).date()


def in_sess(h, sess):
    s, e = sess
    return s <= h < e if s < e else (h >= s or h < e)


# ----------------------------- market helpers -----------------------------

def market_info(symbol):
    s = symbol.upper()
    if "XAU" in s:
        return "Gold", 100.0, lambda c: 0.30
    if "XAG" in s:
        return "Silver", 5000.0, lambda c: 0.03
    if any(x in s for x in ("BTC", "ETH", "SOL", "XRP", "LTC")):
        return "Crypto", 1.0, lambda c: c * 0.0002
    parts = s.split("/")
    if len(parts) == 2 and len(parts[0]) == 3 and len(parts[1]) == 3:
        pip = 0.01 if "JPY" in s else 0.0001
        return "Forex", 100000.0, lambda c: pip
    return "Index / other", 1.0, lambda c: c * 0.00005


def fmt(p):
    if p is None:
        return "-"
    if p >= 1000:
        return f"{p:,.2f}"
    if p >= 10:
        return f"{p:.3f}"
    return f"{p:.5f}"


# ----------------------------- data -----------------------------

def fetch_bars(symbol, interval, api_key):
    q = urllib.parse.urlencode({
        "symbol": symbol, "interval": interval, "outputsize": 5000,
        "timezone": "UTC", "order": "asc", "apikey": api_key,
    })
    req = urllib.request.Request("https://api.twelvedata.com/time_series?" + q,
                                 headers={"User-Agent": "mss-telegram-bot"})
    with urllib.request.urlopen(req, timeout=40) as r:
        data = json.load(r)
    if data.get("status") != "ok":
        raise RuntimeError(data.get("message") or str(data)[:300])
    bars = []
    for v in data.get("values", []):
        ds = v["datetime"]
        fmt_in = "%Y-%m-%d %H:%M:%S" if " " in ds else "%Y-%m-%d"
        t = datetime.strptime(ds, fmt_in).replace(tzinfo=UTC)
        bars.append(Bar(t, float(v["open"]), float(v["high"]), float(v["low"]), float(v["close"])))
    bars.sort(key=lambda b: b.t)
    return bars


def resample(bars, key_fn):
    """Groups bars into a higher timeframe. key_fn(t) -> (key, close_time)."""
    out, closes, cur, cur_key = [], [], None, None
    for b in bars:
        k, close_t = key_fn(b.t)
        if k != cur_key:
            if cur is not None:
                out.append(cur)
            cur = Bar(b.t, b.o, b.h, b.l, b.c)
            cur_key = k
            closes.append(close_t)
        else:
            cur.h = max(cur.h, b.h)
            cur.l = min(cur.l, b.l)
            cur.c = b.c
    if cur is not None:
        out.append(cur)
    return out, closes


def h1_key(t):
    start = t.replace(minute=0, second=0, microsecond=0)
    return start, start + timedelta(hours=1)


def h4_key(t):
    """4H candles that start at 17:00 New York time, like TradingView."""
    off = ny_offset(t)
    shifted = t + off - timedelta(hours=17)
    block = shifted.replace(hour=(shifted.hour // 4) * 4, minute=0, second=0, microsecond=0)
    start = block + timedelta(hours=17) - off
    return (block.date(), block.hour), start + timedelta(hours=4)


def m15_key(t):
    start = t.replace(minute=(t.minute // 15) * 15, second=0, microsecond=0)
    return start, start + timedelta(minutes=15)


def htf_trend(bars, closes, length):
    """Trend after each higher-timeframe candle: +1 up, -1 down, 0 unknown."""
    out, last_h, last_l, b = [], None, None, 0
    for j in range(len(bars)):
        p = j - length
        if p - length >= 0:
            ph = all(bars[p - k].h <= bars[p].h and bars[p + k].h < bars[p].h for k in range(1, length + 1))
            pl = all(bars[p - k].l >= bars[p].l and bars[p + k].l > bars[p].l for k in range(1, length + 1))
            if ph:
                last_h = bars[p].h
            if pl:
                last_l = bars[p].l
        if last_h is not None and bars[j].c > last_h:
            b, last_h = 1, None
        elif last_l is not None and bars[j].c < last_l:
            b, last_l = -1, None
        out.append(b)
    return out


# ----------------------------- the engine -----------------------------

class Setup:
    def __init__(self):
        self.active = False
        self.dir = 0
        self.has_f = self.has_o = self.confl = False
        self.f_top = self.f_bot = self.o_top = self.o_bot = self.origin = 0.0
        self.born = 0
        self.score = 0
        self.grade = ""
        self.why = []

    def zone(self):
        lo = min(self.f_bot if self.has_f else 1e18, self.o_bot if self.has_o else 1e18)
        hi = max(self.f_top if self.has_f else -1e18, self.o_top if self.has_o else -1e18)
        return f"{fmt(lo)} - {fmt(hi)}"


class Trade:
    def __init__(self, d, entry, sl, tp1, tp2, start, grade):
        self.dir, self.entry, self.sl, self.tp1, self.tp2 = d, entry, sl, tp1, tp2
        self.start, self.grade, self.stage, self.r = start, grade, 0, 0.0


class Engine:
    def __init__(self, symbol, bars, tf_minutes):
        self.sym = symbol
        self.bars = bars
        self.tf = timedelta(minutes=tf_minutes)
        self.tf_txt = f"{tf_minutes}m"
        self.swing = 5 if tf_minutes <= 5 else 4
        self.min_leg = 2.5 if tf_minutes <= 5 else 3.0
        self.min_grade = {"A+": 3, "A": 2}.get(QUALITY.upper(), 1)
        self.mkt, self.units, self.spread_fn = market_info(symbol)
        self.events = []
        n = len(bars)

        # ATR
        self.atr = [0.0] * n
        for k in range(n):
            tr = bars[k].h - bars[k].l if k == 0 else max(
                bars[k].h - bars[k].l, abs(bars[k].h - bars[k - 1].c), abs(bars[k].l - bars[k - 1].c))
            if k < ATR_LEN:
                self.atr[k] = (self.atr[k - 1] * k + tr) / (k + 1) if k else tr
            else:
                self.atr[k] = (self.atr[k - 1] * (ATR_LEN - 1) + tr) / ATR_LEN

        # higher timeframes built from the same candles
        src = bars
        if tf_minutes < 15:
            src, _ = resample(bars, m15_key)
        h1, self.h1_close = resample(src, h1_key)
        h4, self.h4_close = resample(src, h4_key)
        self.h1 = h1
        self.h1_trend = htf_trend(h1, self.h1_close, HTF_LEN)
        self.h4_trend = htf_trend(h4, self.h4_close, HTF_LEN)

        # daily / weekly high and low (forex day starts 17:00 New York)
        self.day_keys, self.day_hl = [], {}
        self.week_keys, self.week_hl = [], {}
        for b in bars:
            d = trading_date(b.t)
            w = d.isocalendar()[:2]
            if d not in self.day_hl:
                self.day_keys.append(d)
                self.day_hl[d] = [b.h, b.l]
            else:
                self.day_hl[d][0] = max(self.day_hl[d][0], b.h)
                self.day_hl[d][1] = min(self.day_hl[d][1], b.l)
            if w not in self.week_hl:
                self.week_keys.append(w)
                self.week_hl[w] = [b.h, b.l]
            else:
                self.week_hl[w][0] = max(self.week_hl[w][0], b.h)
                self.week_hl[w][1] = min(self.week_hl[w][1], b.l)
        self.day_idx = {d: i for i, d in enumerate(self.day_keys)}
        self.week_idx = {w: i for i, w in enumerate(self.week_keys)}

        # state
        self.last_h = self.last_l = None
        self.last_h_bar = self.last_l_bar = -1
        self.trend = 0
        self.p_hi, self.p_lo = [], []          # (price, bar) recent swing points
        self.choch_bars = []
        self.bull, self.bear = Setup(), Setup()
        self.trade = None
        self.day = None
        self.week = None
        self.day_n, self.day_r = 0, 0.0
        self.asia_hi = self.asia_lo = self.lon_hi = self.lon_lo = None
        self.prev_asia = self.prev_lon = False
        self.done = dict(pwh=False, pwl=False, pdh=False, pdl=False, lh=False, ll=False, ah=False, al=False)
        self.bear_ref = self.bull_ref = None
        self.bear_ref_bar = self.bull_ref_bar = -1
        self.bear_arm = self.bull_arm = 0
        self.cisd_up = self.cisd_dn = -10 ** 9
        self.last_sign = "-"
        self.n = self.wins = self.losses = 0
        self.net_r = 0.0
        self.b1 = self.b2 = self.gate = 0
        self.in_asia = self.in_lon = self.in_ny = False
        self.choppy = False
        self.day_ok = True
        self.pdh = self.pdl = None

    # ---------- helpers ----------
    def emit(self, i, text):
        self.events.append((self.bars[i].t + self.tf, text))

    def head(self):
        return f"{self.sym} {self.tf_txt}"

    def trend_at(self, closes, trends, t):
        j = bisect_right(closes, t) - 1
        return trends[j] if j >= 0 else 0

    def lots_txt(self, risk_px):
        money = ACCOUNT_SIZE * RISK_PCT / 100.0
        quote_usd = self.sym.upper().endswith("/USD") or self.mkt in ("Crypto", "Index / other")
        if risk_px <= 0 or not quote_usd:
            return f"use your broker's lot calculator (risk ${money:,.0f})"
        lots = money / (risk_px * self.units)
        return f"{lots:.2f} lots (risk ${money:,.0f})"

    def is_ph(self, p, L):
        b = self.bars
        if p - L < 0:
            return False
        return all(b[p - k].h <= b[p].h and b[p + k].h < b[p].h for k in range(1, L + 1))

    def is_pl(self, p, L):
        b = self.bars
        if p - L < 0:
            return False
        return all(b[p - k].l >= b[p].l and b[p + k].l > b[p].l for k in range(1, L + 1))

    def max_body(self, i, d):
        b = self.bars
        return max(max(0.0, (b[k].c - b[k].o) * d) for k in range(max(0, i - 2), i + 1))

    def run_open(self, i, d):
        """Open of the run of candles that made the extreme (for CISD)."""
        b = self.bars
        k = 0
        while k < 10 and i - k > 0 and ((b[i - k].c <= b[i - k].o) if d == -1 else (b[i - k].c >= b[i - k].o)):
            k += 1
        start = k
        while k < 30 and i - k > 0 and ((b[i - k].c > b[i - k].o) if d == -1 else (b[i - k].c < b[i - k].o)):
            k += 1
        if k > start:
            return b[i - (k - 1)].o, i - (k - 1)
        return None, -1

    def equilibrium(self, t):
        j = bisect_right(self.h1_close, t) - 1
        if j < PD_LEN - 1:
            return None
        seg = self.h1[j - PD_LEN + 1:j + 1]
        return (max(x.h for x in seg) + min(x.l for x in seg)) / 2.0

    def sw(self, lv, ext, i, off, d):
        if lv is None:
            return False
        b = self.bars
        if d == 1:
            return ext < lv and (b[i - off].c > lv or (off >= 1 and b[i - off + 1].c > lv))
        return ext > lv and (b[i - off].c < lv or (off >= 1 and b[i - off + 1].c < lv))

    def setup_sweep(self, i, d, ext, off):
        ext_bar = i - off
        if d == 1:
            if self.sw(self.pdl, ext, i, off, 1) or self.sw(self.asia_lo, ext, i, off, 1):
                return True
            return any(pb < ext_bar and self.sw(px, ext, i, off, 1) for px, pb in self.p_lo[-6:])
        if self.sw(self.pdh, ext, i, off, -1) or self.sw(self.asia_hi, ext, i, off, -1):
            return True
        return any(pb < ext_bar and self.sw(px, ext, i, off, -1) for px, pb in self.p_hi[-6:])

    def blocked(self, d, entry, tp1, risk):
        if not USE_ROOM:
            return False
        near = entry + d * 0.2 * risk

        def between(lv, lo, hi):
            return lv is not None and lo < lv < hi
        if d == 1:
            return between(self.pdh, near, tp1) or between(self.asia_hi, near, tp1)
        return between(self.pdl, tp1, near) or between(self.asia_lo, tp1, near)

    # ---------- grade the CHoCH ----------
    def build(self, i, d, brk_bar, brk_lvl, atr_v, disp_r, in_kz):
        b = self.bars
        s = Setup()
        span = min(i - brk_bar, 150)
        ext, off = (b[i].l if d == 1 else b[i].h), 0
        for k in range(span + 1):
            if d == 1 and b[i - k].l < ext:
                ext, off = b[i - k].l, k
            elif d == -1 and b[i - k].h > ext:
                ext, off = b[i - k].h, k
        f_t = f_b = None
        if off >= 2:
            for k in range(off - 1):
                a, c = i - k, i - k - 2
                if d == 1 and b[a].l > b[c].h and b[a].l - b[c].h >= MIN_FVG * atr_v:
                    f_t, f_b = b[a].l, b[c].h
                    break
                if d == -1 and b[a].h < b[c].l and b[c].l - b[a].h >= MIN_FVG * atr_v:
                    f_t, f_b = b[c].l, b[a].h
                    break
        ob_off = off
        for j in range(4):
            idx = i - (off + j)
            if idx < 0:
                break
            if (d == 1 and b[idx].c < b[idx].o) or (d == -1 and b[idx].c > b[idx].o):
                ob_off = off + j
                break
        ob_t, ob_b = b[i - ob_off].h, b[i - ob_off].l
        fvg = f_t is not None
        confl = fvg and f_t >= ob_b and f_b <= ob_t
        z_mid = (f_t + f_b) / 2 if fvg else (ob_t + ob_b) / 2
        sweep = self.setup_sweep(i, d, ext, off)
        eq = self.equilibrium(b[i].t)
        pd = eq is not None and (z_mid < eq if d == 1 else z_mid > eq)
        strong = disp_r >= DISP_MULT * 1.5
        small = abs(brk_lvl - ext) / atr_v < self.min_leg
        score = (25 if sweep else 0) + (20 if confl else 0) + (20 if pd else 0) + (20 if in_kz else 0) + (15 if strong else 0)
        g = 3 if score >= 65 else 2 if score >= 45 else 1
        if small:
            g = 1
        why = []
        if sweep: why.append("Liquidity sweep")
        if confl: why.append("FVG + order block")
        if pd: why.append("Cheap price" if d == 1 else "Expensive price")
        if in_kz: why.append("Active session")
        if strong: why.append("Very strong move")
        if small: why.append("Small shift")
        if not (fvg and disp_r >= DISP_MULT and g >= self.min_grade):
            return s
        s.active, s.dir, s.has_f, s.has_o, s.confl = True, d, True, True, confl
        s.origin, s.born, s.score = ext, i, score
        s.f_top, s.f_bot, s.o_top, s.o_bot = f_t, f_b, ob_t, ob_b
        s.grade = "A+" if g == 3 else "A" if g == 2 else "B"
        s.why = why
        return s

    # ---------- wait for the retest ----------
    def manage(self, s, i, atr_v, can_enter):
        b = self.bars[i]
        if not s.active or i <= s.born:
            return None
        bull = s.dir == 1
        if s.has_f and (b.c < s.f_bot if bull else b.c > s.f_top):
            s.has_f = False
        if s.has_o and (b.c < s.o_bot if bull else b.c > s.o_top):
            s.has_o = False
        if (not s.has_f and not s.has_o) or i - s.born > MAX_WAIT or (b.c < s.origin if bull else b.c > s.origin):
            s.active = False
            return None
        mid = (b.h + b.l) / 2
        rej = (b.c > b.o and b.c >= mid) if bull else (b.c < b.o and b.c <= mid)
        f_hit = s.has_f and rej and ((b.l <= s.f_top and b.c > s.f_bot) if bull else (b.h >= s.f_bot and b.c < s.f_top))
        o_hit = s.has_o and rej and ((b.l <= s.o_top and b.c > s.o_bot) if bull else (b.h >= s.o_bot and b.c < s.o_top))
        if (f_hit or o_hit) and can_enter:
            entry = b.c + s.dir * self.spread_fn(b.c)
            if bull:
                edge = min(s.f_bot if f_hit else 1e18, s.o_bot if o_hit else 1e18)
                sl = edge - SL_BUF * atr_v
            else:
                edge = max(s.f_top if f_hit else -1e18, s.o_top if o_hit else -1e18)
                sl = edge + SL_BUF * atr_v
            risk = abs(entry - sl)
            tp1 = entry + s.dir * RR1 * risk
            if (sl < entry if bull else sl > entry) and risk <= MAX_STOP * atr_v and not self.blocked(s.dir, entry, tp1, risk):
                s.active = False
                return sl, ("FVG retest" if f_hit else "OB retest")
        return None

    def open_trade(self, i, d, sl, grade, kind):
        c = self.bars[i].c
        entry = c + d * self.spread_fn(c)
        risk = abs(entry - sl)
        rr_b = max(RR1, RR2)
        tr = Trade(d, entry, sl, entry + d * RR1 * risk, entry + d * rr_b * risk, i, grade)
        self.trade = tr
        self.day_n += 1
        if ALERT_ENTRY:
            side = "🟢 BUY" if d == 1 else "🔴 SELL"
            self.emit(i, (
                f"{side} {self.head()} - {grade} ({kind})\n"
                f"Entry: {fmt(entry)}\n"
                f"Stop loss: {fmt(sl)}\n"
                f"Target 1: {fmt(tr.tp1)}  ({RR1:g}R, close {PARTIAL_PCT:g}%)\n"
                f"Target 2: {fmt(tr.tp2)}  ({rr_b:g}R)\n"
                f"Lot size: {self.lots_txt(risk)}\n"
                f"Open your chart and check price is still near the entry before you trade."))

    def update_trade(self, i):
        tr = self.trade
        if tr is None or i <= tr.start:
            return
        b = self.bars[i]
        bull = tr.dir == 1
        pf = PARTIAL_PCT / 100.0
        rr_b = max(RR1, RR2)
        stop = tr.entry if (tr.stage == 1 and BREAK_EVEN) else tr.sl
        stop_hit = b.l <= stop if bull else b.h >= stop
        tp1_hit = b.h >= tr.tp1 if bull else b.l <= tr.tp1
        tp2_hit = b.h >= tr.tp2 if bull else b.l <= tr.tp2
        res = None
        if tr.stage == 0:
            if stop_hit:
                tr.r, res = -1.0, "LOSS"
            elif tp1_hit:
                tr.r, tr.stage = pf * RR1, 1
                if pf >= 0.999:
                    res = "WIN"
                elif tp2_hit:
                    tr.r += (1 - pf) * rr_b
                    res = "FULL WIN"
                elif ALERT_RESULT:
                    extra = f" Move your stop to entry {fmt(tr.entry)}." if BREAK_EVEN else ""
                    self.emit(i, f"🎯 {self.head()}: target 1 hit (+{tr.r:.1f}R so far).{extra}")
        else:
            if stop_hit:
                tr.r += (1 - pf) * (0.0 if BREAK_EVEN else -1.0)
                res = "PART WIN"
            elif tp2_hit:
                tr.r += (1 - pf) * rr_b
                res = "FULL WIN"
        if res is None:
            return
        self.trade = None
        self.n += 1
        self.net_r += tr.r
        self.day_r += tr.r
        if tr.r > 0.0001:
            self.wins += 1
        elif tr.r < -0.0001:
            self.losses += 1
        if ALERT_RESULT:
            icon = "✅" if tr.r > 0.0001 else ("❌" if tr.r < -0.0001 else "➖")
            self.emit(i, f"{icon} {self.head()}: {'BUY' if bull else 'SELL'} closed - {res} {tr.r:+.1f}R")

    # ---------- one closed candle ----------
    def process(self, i):
        bars = self.bars
        b = bars[i]
        atr_v = self.atr[i]
        if atr_v <= 0:
            return
        t = b.t
        ny = to_ny(t)
        in_asia, in_lon, in_ny = in_sess(ny.hour, ASIA), in_sess(ny.hour, LONDON), in_sess(ny.hour, NEW_YORK)
        in_kz = in_lon or in_ny
        b1 = self.trend_at(self.h4_close, self.h4_trend, t)
        b2 = self.trend_at(self.h1_close, self.h1_trend, t)
        gate = b1 if b1 == b2 else 0
        self.b1, self.b2, self.gate = b1, b2, gate
        self.in_asia, self.in_lon, self.in_ny = in_asia, in_lon, in_ny

        # new day / week, key levels
        d = trading_date(t)
        w = d.isocalendar()[:2]
        if d != self.day:
            self.day, self.day_n, self.day_r = d, 0, 0.0
            self.done["pdh"] = self.done["pdl"] = False
        if w != self.week:
            self.week = w
            self.done["pwh"] = self.done["pwl"] = False
        di = self.day_idx[d]
        self.pdh, self.pdl = (self.day_hl[self.day_keys[di - 1]] if di > 0 else (None, None))
        wi = self.week_idx[w]
        pwh, pwl = (self.week_hl[self.week_keys[wi - 1]] if wi > 0 else (None, None))

        if in_asia and not self.prev_asia:
            self.asia_hi, self.asia_lo = b.h, b.l
        elif in_asia:
            self.asia_hi, self.asia_lo = max(self.asia_hi, b.h), min(self.asia_lo, b.l)
        if in_lon and not self.prev_lon:
            self.lon_hi, self.lon_lo = b.h, b.l
        elif in_lon:
            self.lon_hi, self.lon_lo = max(self.lon_hi, b.h), min(self.lon_lo, b.l)
        self.prev_asia, self.prev_lon = in_asia, in_lon
        if in_asia:
            self.done["ah"] = self.done["al"] = False
        if in_lon:
            self.done["lh"] = self.done["ll"] = False

        # swing points
        p = i - self.swing
        if self.is_ph(p, self.swing):
            self.last_h, self.last_h_bar = bars[p].h, p
            self.p_hi = (self.p_hi + [(bars[p].h, p)])[-12:]
        if self.is_pl(p, self.swing):
            self.last_l, self.last_l_bar = bars[p].l, p
            self.p_lo = (self.p_lo + [(bars[p].l, p)])[-12:]

        # ---------- key-level sweeps + CISD ----------
        sell_signs = not SIGN_TREND or gate == -1
        buy_signs = not SIGN_TREND or gate == 1
        sw_hi = sw_lo = ""
        for key, lv, name, active in (("pwh", pwh, "last week high", True), ("pdh", self.pdh, "yesterday high", True),
                                      ("lh", self.lon_hi, "London high", not in_lon), ("ah", self.asia_hi, "Asia high", not in_asia)):
            if active and not self.done[key] and lv is not None and b.h > lv:
                self.done[key] = True
                if b.c < lv and not sw_hi:
                    sw_hi = name
        for key, lv, name, active in (("pwl", pwl, "last week low", True), ("pdl", self.pdl, "yesterday low", True),
                                      ("ll", self.lon_lo, "London low", not in_lon), ("al", self.asia_lo, "Asia low", not in_asia)):
            if active and not self.done[key] and lv is not None and b.l < lv:
                self.done[key] = True
                if b.c > lv and not sw_lo:
                    sw_lo = name
        if sw_hi:
            self.bear_ref, self.bear_ref_bar = self.run_open(i, -1)
            self.bear_arm = i
            if sell_signs:
                self.last_sign = f"BSL sweep ({sw_hi})"
                if ALERT_SIGNS:
                    self.emit(i, f"💧 {self.head()}: buy-side liquidity sweep of {sw_hi}. Watch for a bearish CISD.")
        if sw_lo:
            self.bull_ref, self.bull_ref_bar = self.run_open(i, 1)
            self.bull_arm = i
            if buy_signs:
                self.last_sign = f"SSL sweep ({sw_lo})"
                if ALERT_SIGNS:
                    self.emit(i, f"💧 {self.head()}: sell-side liquidity sweep of {sw_lo}. Watch for a bullish CISD.")
        if self.bear_ref is not None:
            if i - self.bear_arm > CISD_WAIT:
                self.bear_ref = None
            elif b.c < self.bear_ref:
                self.cisd_dn = i
                if sell_signs:
                    self.last_sign = "Bearish CISD"
                    if ALERT_SIGNS:
                        self.emit(i, f"🟠 {self.head()}: bearish CISD after the sweep. Get ready for a CHoCH down.")
                self.bear_ref = None
        if self.bull_ref is not None:
            if i - self.bull_arm > CISD_WAIT:
                self.bull_ref = None
            elif b.c > self.bull_ref:
                self.cisd_up = i
                if buy_signs:
                    self.last_sign = "Bullish CISD"
                    if ALERT_SIGNS:
                        self.emit(i, f"🟠 {self.head()}: bullish CISD after the sweep. Get ready for a CHoCH up.")
                self.bull_ref = None

        # ---------- CHoCH ----------
        up_brk = self.last_h is not None and b.c > self.last_h
        dn_brk = (not up_brk) and self.last_l is not None and b.c < self.last_l
        choch_dir, brk_lvl, brk_bar = 0, None, -1
        if up_brk:
            brk_lvl, brk_bar = self.last_h, self.last_h_bar
            if self.trend == -1:
                choch_dir = 1
            self.last_h, self.trend = None, 1
        elif dn_brk:
            brk_lvl, brk_bar = self.last_l, self.last_l_bar
            if self.trend == 1:
                choch_dir = -1
            self.last_l, self.trend = None, -1
        if choch_dir:
            self.choch_bars = (self.choch_bars + [i])[-50:]
            self.bull.active = self.bear.active = False
            if choch_dir == gate:
                s = self.build(i, choch_dir, brk_bar, brk_lvl, atr_v, self.max_body(i, choch_dir) / atr_v, in_kz)
                if choch_dir == 1:
                    self.bull = s
                else:
                    self.bear = s
                if s.active:
                    why = list(s.why)
                    cisd_bar = self.cisd_up if choch_dir == 1 else self.cisd_dn
                    if i - cisd_bar <= CISD_WAIT:
                        why.append("CISD")
                    self.last_sign = f"{'Bullish' if choch_dir == 1 else 'Bearish'} CHoCH {s.grade}"
                    if ALERT_CHOCH:
                        side = "BUY" if choch_dir == 1 else "SELL"
                        arrow = "⬆️" if choch_dir == 1 else "⬇️"
                        self.emit(i, (
                            f"{arrow} {self.head()} - {'Bullish' if choch_dir == 1 else 'Bearish'} CHoCH {s.grade} ({s.score})\n"
                            f"Reasons: {', '.join(why) if why else '-'}\n"
                            f"{side} ZONE: {s.zone()}\n"
                            f"Get ready. Wait for price to come back into the zone; an entry message follows if it does."))

        # ---------- trades ----------
        self.update_trade(i)
        self.day_ok = (MAX_PER_DAY == 0 or self.day_n < MAX_PER_DAY) and (DAY_STOP_R == 0 or self.day_r > -DAY_STOP_R)
        self.choppy = USE_CHOP and sum(1 for x in self.choch_bars if x > i - CHOP_BARS) >= CHOP_MAX
        sess_ok = (not KZ_ONLY) or in_kz
        slot = self.trade is None
        can_buy = sess_ok and self.day_ok and slot and not self.choppy and gate == 1
        can_sell = sess_ok and self.day_ok and slot and not self.choppy and gate == -1
        for s, can in ((self.bull, can_buy), (self.bear, can_sell)):
            grade = s.grade
            res = self.manage(s, i, atr_v, can)
            if res:
                self.open_trade(i, s.dir, res[0], grade, res[1])
                break

    def run(self):
        start = max(260, len(self.bars) - 4500)
        for i in range(start, len(self.bars)):
            self.process(i)

    def status(self):
        def tt(x):
            return "UP" if x == 1 else "DOWN" if x == -1 else "NOT CLEAR"
        look = "BUYS only" if self.gate == 1 else "SELLS only" if self.gate == -1 else "Nothing"
        sess = "London (active)" if self.in_lon else "New York (active)" if self.in_ny else "Asia" if self.in_asia else "Quiet hours"
        if self.trade:
            tr = self.trade
            now = f"IN A {'BUY' if tr.dir == 1 else 'SELL'} TRADE" + (" - target 1 hit" if tr.stage == 1 else "")
        elif not self.day_ok:
            now = "STOP - daily limit reached"
        elif self.choppy:
            now = "WAIT - market is choppy"
        elif self.bull.active:
            now = f"BUY setup {self.bull.grade} - wait for retest of {self.bull.zone()}"
        elif self.bear.active:
            now = f"SELL setup {self.bear.grade} - wait for retest of {self.bear.zone()}"
        elif self.gate == 0:
            now = "NO TRADE - trends disagree"
        else:
            now = "WAIT - no setup yet"
        last = self.bars[-1]
        lines = [
            f"📊 {self.head()} status ({self.mkt})",
            f"Last closed candle: {to_ny(last.t + self.tf):%a %H:%M} New York, close {fmt(last.c)}",
            f"Trend 4H: {tt(self.b1)} | Trend 1H: {tt(self.b2)}",
            f"I look for: {look}",
            f"Session: {sess}",
            f"Last ICT sign: {self.last_sign}",
            f"NOW: {now}",
        ]
        if self.trade:
            tr = self.trade
            lines.append(f"Entry {fmt(tr.entry)} | Stop {fmt(tr.sl)} | T1 {fmt(tr.tp1)} | T2 {fmt(tr.tp2)}")
        verdict = " (too few to judge)" if self.n < 20 else ""
        days = (self.bars[-1].t - self.bars[max(260, len(self.bars) - 4500)].t).days
        lines.append(f"Past trades (last {days} days): {self.n} ({self.wins} won, {self.losses} lost), total {self.net_r:+.1f}R{verdict}")
        return "\n".join(lines)


# ----------------------------- sending -----------------------------

DEST = {"ntfy": "", "tg_token": "", "tg_chat": ""}


def tg_call(token, method, params):
    data = urllib.parse.urlencode(params).encode()
    req = urllib.request.Request(f"https://api.telegram.org/bot{token}/{method}", data=data)
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def ntfy_send(topic, text):
    first = text.splitlines()[0] if text else "MSS alert"
    # HTTP headers must be plain ASCII, so the emojis go in the message body only
    title = first.encode("ascii", "ignore").decode().strip(" -:") or "MSS alert"
    urgent = any(x in first for x in ("BUY", "SELL", "CHoCH"))
    req = urllib.request.Request(
        "https://ntfy.sh/" + urllib.parse.quote(topic),
        data=text[:4000].encode("utf-8"),
        headers={"Title": title[:120], "Priority": "high" if urgent else "default",
                 "Tags": "chart_with_upwards_trend"})
    with urllib.request.urlopen(req, timeout=30) as r:
        r.read()


def send(text):
    ok = False
    if DEST["ntfy"]:
        try:
            ntfy_send(DEST["ntfy"], text)
            ok = True
        except urllib.error.URLError as e:
            print("ntfy error:", e)
    if DEST["tg_token"] and DEST["tg_chat"]:
        try:
            tg_call(DEST["tg_token"], "sendMessage",
                    {"chat_id": DEST["tg_chat"], "text": text[:4000], "disable_web_page_preview": "true"})
            ok = True
        except urllib.error.URLError as e:
            print("Telegram error:", e)
    print(("Sent: " if ok else "NOT sent: ") + (text.splitlines()[0] if text else ""))


def show_chat_ids(token):
    print("TELEGRAM_CHAT_ID is not set yet. Looking for chats that wrote to your bot...")
    res = tg_call(token, "getUpdates", {})
    found = {}
    for u in res.get("result", []):
        msg = u.get("message") or u.get("channel_post") or {}
        chat = msg.get("chat") or {}
        if "id" in chat:
            found[chat["id"]] = chat.get("first_name") or chat.get("title") or ""
    if not found:
        print("No messages found. Open your bot in Telegram, press START, send it 'hi', then run this again.")
    for cid, name in found.items():
        print(f"YOUR CHAT ID: {cid}   (chat: {name})")
        print("Copy the number above into the GitHub secret TELEGRAM_CHAT_ID.")


# ----------------------------- main -----------------------------

def load_state():
    try:
        with open(STATE_FILE) as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_state(state):
    with open(STATE_FILE, "w") as f:
        json.dump(state, f, indent=2, sort_keys=True)
        f.write("\n")


def main():
    mode = (sys.argv[1] if len(sys.argv) > 1 else "scan").strip().lower()
    DEST["ntfy"] = os.environ.get("NTFY_TOPIC", "").strip()
    DEST["tg_token"] = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    DEST["tg_chat"] = os.environ.get("TELEGRAM_CHAT_ID", "").strip()
    api_key = os.environ.get("TWELVEDATA_API_KEY", "").strip()
    if DEST["tg_token"] and not DEST["tg_chat"]:
        show_chat_ids(DEST["tg_token"])
    if not DEST["ntfy"] and not (DEST["tg_token"] and DEST["tg_chat"]):
        sys.exit("No way to reach your phone yet: add the NTFY_TOPIC secret (see the setup guide).")
    if not api_key:
        send("⚠️ MSS bot: the TWELVEDATA_API_KEY secret is missing. See the setup guide.")
        sys.exit(1)

    tf_minutes = 5 if TIMEFRAME.startswith("5") else 15
    interval = "5min" if tf_minutes == 5 else "15min"
    state = load_state()
    last_sent = state.setdefault("last_sent", {})
    errors = state.setdefault("error_day", {})
    now = datetime.now(UTC)
    today = now.date().isoformat()
    failed = False

    for idx, sym in enumerate(SYMBOLS):
        if idx > 0:
            time.sleep(8)  # stay inside the free plan's 8 credits per minute
        try:
            bars = fetch_bars(sym, interval, api_key)
        except Exception as e:  # noqa: BLE001
            print(f"Data error for {sym}: {e}")
            failed = True
            if mode == "test" or errors.get(sym) != today:
                errors[sym] = today
                send(f"⚠️ MSS bot could not get {sym} candles from Twelve Data:\n{e}")
            continue
        bars = [b for b in bars if b.t + timedelta(minutes=tf_minutes) <= now]  # closed candles only
        if len(bars) < 400:
            send(f"⚠️ MSS bot: only {len(bars)} candles received for {sym}. Not enough to scan yet.")
            continue

        eng = Engine(sym, bars, tf_minutes)
        eng.run()
        newest = bars[-1].t + timedelta(minutes=tf_minutes)

        if mode == "test":
            send("✅ MSS bot is connected.\n\n" + eng.status())
            last_sent.setdefault(sym, newest.isoformat())
            continue

        prev = last_sent.get(sym)
        if prev is None:
            last_sent[sym] = newest.isoformat()
            send(f"👀 MSS bot started watching {sym} on {interval}.\n\n" + eng.status())
            continue
        prev_t = datetime.fromisoformat(prev)
        for close_t, text in eng.events:
            if close_t <= prev_t:
                continue
            age = (now - close_t).total_seconds() / 60
            if age > MAX_AGE_MINUTES:
                print(f"Skipped old event ({age:.0f} min): {text.splitlines()[0]}")
                continue
            ny_close = to_ny(close_t)
            stamp = f"\n🕒 Candle closed {ny_close:%H:%M} New York time"
            if age > LATE_MINUTES:
                stamp += f" (late by {age:.0f} min, check the chart first)"
            send(text + stamp)
        if newest > prev_t:
            last_sent[sym] = newest.isoformat()

    state["heartbeat"] = today  # keeps the repository active so GitHub keeps the schedule on
    save_state(state)
    if failed and mode == "test":
        sys.exit(1)


if __name__ == "__main__":
    main()
