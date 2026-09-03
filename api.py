#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""金书群侠传 云存档服务端 (单文件, python3 stdlib only)

端点 (统一响应 JSON {"code":0,"msg":"ok","data":...}; blob 类端点直接回原始字节):
  GET  /api/save/ping                          健康检查(ESA 缓存验证用)
  POST /api/save/hello    {code?,name?}             握手:新建或绑定云码,回全量清单
  POST /api/save/register {user,pass,invite}        注册账号(需邀请码,一码一用;自动生成云码)
  POST /api/save/login    {user,pass}               登录,回 {user,code}
  POST /api/save/slot?code=&slot=&md5=&name=&chain=&vg=   body=Save_N.sav 原始字节
  GET  /api/save/slot?code=&slot=&ver=&t=               回 .sav 原始字节(ver缺省=最新)
  POST /api/save/profile?code=&name=&md5=               body=档案文件字节
  GET  /api/save/profile?code=&name=&t=                 回档案文件字节
  POST /api/save/tower?code=&floor=&name=               天关层数上报(只涨不跌)
  GET  /api/save/tower?code=&top=50                     天关全服排行榜(前N+我的名次)
  POST /api/save/pvp/snap?code=&name=&n=&pw=&pw2=&md5=  body=镜像快照(Lua文本,≤512KB)
  GET  /api/save/pvp/board?code=&top=50                 论剑台榜(全员可挑战,games<5行rank=null)
  GET  /api/save/pvp/me?code=                          我的资料(玩家名/称号/论剑币/战绩)
  GET  /api/save/pvp/shop?code=                        商店目录+已购+余额
  POST /api/save/pvp/name          body {code,name}     设玩家名(首免费,改名200币,全服唯一)
  POST /api/save/pvp/buy?code=&id=                      购买(原子扣币;once类不可重复)
  POST /api/save/pvp/title?code=&text=                  切换已拥有称号(空=取下)
  POST /api/save/pvp/presence?code=&leave=&x=&y=&dir=&walk=  论剑台在线心跳(v2同屏:带坐标TTL 6s/旧40s,响应带位置/战绩/pid)
  GET  /api/save/pvp/challenge?code=&foe=<pid>          发挑战令牌(当日20次,6h时效)
  GET  /api/save/pvp/snap?code=&foe=<pid>&tok=          下载对手镜像(需有效令牌)
  POST /api/save/pvp/report?code=&foe=<pid>&mode=&win=&tok=  战报+ELO结算(令牌一局一核销)

约定: 云码 12 位(去 0O1I),库内无连字符;请求可带连字符。所有响应 no-store。
账号: user 2~16 字符(\w 含中文/字母/数字/下划线/连字符), pass 4~64;
     pbkdf2_hmac sha256 6万轮+独立盐; 连错 8 次锁 15 分钟。
"""
import hashlib
import json
import os
import re
import secrets
import sqlite3
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

ROOT = os.environ.get("CLOUDSAVE_ROOT", "/srv/cloudsave")  # 本地测试可覆盖
DB_PATH = os.path.join(ROOT, "cloud.db")
BLOB_DIR = os.path.join(ROOT, "blobs")
PORT = 8765

CODE_CHARS = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
CODE_RE = re.compile(r"^[" + CODE_CHARS + r"]{12}$")
INVITE_CHARS = CODE_CHARS
INVITE_RE = re.compile(r"^[" + INVITE_CHARS + r"]{8}$")   # 邀请码8位,比云码短好输
SLOT_MIN, SLOT_MAX = 1, 10
PROFILE_NAMES = ("achievements", "hero_archive", "WeeklyAwards", "WeekV2")
MAX_SLOT_BODY = 8 << 20        # 槽档实测 ~400KB, 留足余量
MAX_PROFILE_BODY = 2 << 20     # 档案 4 件合计 ~250KB
MAX_VERSIONS = 3               # 每槽保留版本数
NAME_MAX = 24                  # 主角名截断(字节)
TOWER_TOP_MAX = 100            # 榜单单次返回条数上限
TAMPER_TP_MAX = 99999          # 客户端上报的篡改计数上限(防乱填)
DRIFT_FLAG_MIN = 3             # 漂移计数达到该值才记标(给正常杂音留余量)

PVP_SNAP_MAX = 512 << 10       # 镜像快照上限(实测6人≈130KB,留余量)
PVP_TEAM_MAX = 6               # 镜像成员上限(6v6)
PVP_PW_MAX = 5000000           # 战力值硬顶(防乱填)
PVP_TOP_MAX = 100              # 榜单单次返回条数上限
PVP_TOK_TTL = 6 * 3600         # 挑战令牌时效
PVP_TOK_DAILY = 20             # 每日令牌发放上限(含放弃/强退,防刷)
PVP_COUNT_DAILY = 10           # 每日计分场数上限
PVP_SAME_FOE_DAILY = 2         # 同对手每日计分场次上限(防小号互刷)
PVP_BOARD_MIN_GAMES = 5        # 上榜门槛(计分局数)
ELO_FLOOR = 100                # 积分下限

# ---- 论剑币商店 ----
# thing=游戏物品代号(客户端 instruct_2 发放;银两=174)。once=一次性(仅称号;名剑不限购,可重复买作合成材料)。
# daily=每日限购件数(按pvp_buy流水当日计数,跨日恢复;无daily且once=0=不限购)。
PVP_SHOP = [
    {"id": "herb_heiyu",   "kind": "thing", "thing": 2,    "num": 1,
     "name": "黑玉断续膏", "desc": "恢复大量生命", "price": 40,  "once": 0, "daily": 5},
    {"id": "herb_yulu",    "kind": "thing", "thing": 5,    "num": 1,
     "name": "九花玉露丸", "desc": "恢复较多内力", "price": 40,  "once": 0, "daily": 5},
    {"id": "herb_xuelian", "kind": "thing", "thing": 17,   "num": 1,
     "name": "天山雪莲",   "desc": "生命上限+50",  "price": 100, "once": 0, "daily": 5},
    {"id": "herb_lingzhi", "kind": "thing", "thing": 14,   "num": 1,
     "name": "千年灵芝",   "desc": "体质+1",       "price": 500, "once": 0, "daily": 2},
    {"id": "herb_renshen", "kind": "thing", "thing": 16,   "num": 1,
     "name": "千年人参",   "desc": "随机属性+10",  "price": 150, "once": 0, "daily": 5},
    {"id": "herb_zhuha",   "kind": "thing", "thing": 26,   "num": 1,
     "name": "莽牯朱蛤",   "desc": "百毒不侵",     "price": 300, "once": 0, "daily": 5},
    {"id": "gold5000",     "kind": "gold",  "thing": 174,  "num": 5000,
     "name": "白银五千两", "desc": "直接入账",     "price": 100, "once": 0},
]
for _tid, _tn, _td in [
        (631, "轩辕剑", "圣道之剑"), (632, "湛卢剑", "仁道之剑"),
        (633, "赤霄剑", "帝道之剑"), (634, "太阿剑", "威道之剑"),
        (635, "龙渊剑", "诚信高洁之剑"), (636, "干将剑", "挚情雄剑"),
        (637, "莫邪剑", "挚情雌剑"), (638, "鱼肠剑", "勇绝之剑"),
        (639, "纯钧剑", "尊贵无双之剑"), (640, "承影剑", "优雅之剑")]:
    _xy = _tid == 631
    PVP_SHOP.append({"id": "sword%d" % _tid, "kind": "thing", "thing": _tid,
                     "num": 1, "name": _tn,
                     "desc": ("轩辕收集线材料1★" if _xy
                              else "十大名剑·" + _td)
                             + "·1★合成材料·可重复购买·两把可合成升星(满星折精魄)·存入论剑台仓库",
                     "price": 10000, "once": 0})
for _tt in ["剑神", "刀王", "拳霸", "医仙", "毒尊", "酒仙"]:
    PVP_SHOP.append({"id": "title_" + _tt, "kind": "title", "text": _tt,
                     "name": "称号·" + _tt, "desc": "榜单与头顶显示", "price": 4000,
                     "once": 1})
PVP_SHOP_IDX = {it["id"]: it for it in PVP_SHOP}
# ---- 道具目录数据化(2026-09-03):tools/gen_thingext.py 从DB档物品表+overlay生成
# items.json,启动时叠加进商店目录(同id后者胜、新id追加;文件缺席=纯内置,行为
# 不变)。以后加商店道具=改 overlay/DB 重跑生成器+部署 items.json,不动api.py。
# 测试可用环境变量 CLOUDSAVE_ITEMS_JSON 指到临时文件。


def _load_items_json():
    path = os.environ.get("CLOUDSAVE_ITEMS_JSON") or os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "items.json")
    try:
        with open(path, "r", encoding="utf-8") as f:
            extra = json.load(f).get("items", [])
    except Exception:
        return []
    if not isinstance(extra, list):
        return []
    return [it for it in extra if isinstance(it, dict) and it.get("id")]


_extra = _load_items_json()
if _extra:
    _ex = {it["id"]: it for it in _extra}
    PVP_SHOP = [_ex.pop(it["id"], None) or it for it in PVP_SHOP]
    PVP_SHOP.extend(_ex.values())
    PVP_SHOP_IDX = {it["id"]: it for it in PVP_SHOP}
# ---- 服务端可验证成就(领取端点自查资格;aid=客户端成就槽位,须与 CC.Personcj 布局一致) ----
# cond: ("tower",层数)/("wins",胜场)/("score",ELO)/("games",局数)/("wtop",)/("mtop3",)/("swords",种数)
# 奖励: coin=论剑币 / title=称号(直接佩戴);客户端解锁展示,领取时上报此处验发
PVP_ACH = [
    # 天关系·称号档(层内属性/物品档走客户端发放)
    {"aid": 14, "name": "通天者",   "cond": ("tower", 1000), "title": "通天者"},
    {"aid": 15, "name": "摘星者",   "cond": ("tower", 1500), "title": "摘星者"},
    {"aid": 16, "name": "踏破凌霄", "cond": ("tower", 2000), "title": "踏破凌霄"},
    # 论剑系·胜场
    {"aid": 17, "name": "初试锋芒", "cond": ("wins", 1),    "coin": 50},
    {"aid": 18, "name": "小有名气", "cond": ("wins", 10),   "coin": 100},
    {"aid": 19, "name": "剑台常客", "cond": ("wins", 50),   "coin": 200},
    {"aid": 20, "name": "百胜之师", "cond": ("wins", 100),  "coin": 300},
    {"aid": 21, "name": "两百强",   "cond": ("wins", 200),  "coin": 500},
    {"aid": 22, "name": "五百胜",   "cond": ("wins", 500),  "coin": 1000},
    # 论剑系·ELO
    {"aid": 23, "name": "登堂入室", "cond": ("score", 1100), "coin": 50},
    {"aid": 24, "name": "炉火纯青", "cond": ("score", 1200), "coin": 100},
    {"aid": 25, "name": "出类拔萃", "cond": ("score", 1300), "coin": 150},
    {"aid": 26, "name": "登峰造极", "cond": ("score", 1400), "coin": 300},
    {"aid": 27, "name": "独孤求败", "cond": ("score", 1500), "coin": 500},
    {"aid": 28, "name": "剑尊",     "cond": ("score", 1600), "title": "剑尊"},
    # 论剑系·榜/收集
    {"aid": 29, "name": "剑台十杰",   "cond": ("wtop",),     "coin": 500},
    {"aid": 30, "name": "月赛领奖台", "cond": ("mtop3",),    "coin": 1000},
    {"aid": 31, "name": "名剑收藏家", "cond": ("swords", 5), "coin": 800},
    {"aid": 32, "name": "百战不殆",   "cond": ("games", 100), "coin": 400},
]
PVP_ACH_IDX = {a["aid"]: a for a in PVP_ACH}
# ---- 周目成就·物品档(客户端槽位33-44中的物品条目) ----
# 周目数服务端无法核验 → 信任客户端判定,台账一次性(award_once period='ach'),
# 每账号每条只发一次,上限受槽位数约束。物品直接入论剑仓库(acc_item)。
# iid/数量必须与客户端 CC.Personcj 同槽位一致(8=天王保命丹 5=九花玉露丸)。
ACH_TRUST = {
    34: (8, 2),   # 再战江湖: 天王保命丹×2
    36: (5, 2),   # 四海为家: 九花玉露丸×2
    38: (8, 3),   # 六合风云: 天王保命丹×3
    40: (5, 3),   # 八面威风: 九花玉露丸×3
    42: (8, 5),   # 十全十美: 天王保命丹×5
    44: (5, 5),   # 轮回证道: 九花玉露丸×5
}
PVP_NAME_COST = 200            # 改名费(首次免费);论剑币
PVP_NAME_MIN, PVP_NAME_MAX = 2, 8   # 玩家名长度(字符)
PVP_COIN_WIN, PVP_COIN_WIN_BOT, PVP_COIN_LOSS = 30, 15, 5
# 日阶梯(当日真人计分胜场→币,即时发放;含首胜,旧+20首胜并入)
PVP_DAY_TIERS = ((1, 50), (3, 30), (5, 50))
# 周阶梯(周内真人计分胜场→币,周结算时发放)
PVP_WEEK_TIERS = ((5, 100), (10, 150), (20, 250))
PVP_WEEK_TOP_TITLE = "剑台十杰"   # 周ELO榜前十称号(下轮替换旧持有者)

# ---- 十大名剑星级体系(单机零获取途径,全走服务端) ----
# 2026-09-03同名梯子改版(用户拍板"全套同名2-10★+精魄可喂任意名剑"):
# 同名+同名(非轩辕)合成该剑升星;轩辕+轩辕/混名仍熔成轩辕收集线。
# 631-640 = 原版十大名剑(商店基础版,全是1★材料剑,全部不限购可重复买);
# 661-690 = 名剑月赛星级版: 661+(名剑序号-1)*3+{0,1,2} → 5★/4★/3★(星级=装备档,不可升级);
# 691-699 = 轩辕剑收集线2★~10★(收集线剑池内只留一把;台账记历史最高星,取出不亏);
# 700 = 名剑精魄(通用材料):满星轩辕额外所得按星折算;+1★耗XY_FEED_COST枚,可喂任意名剑;
# 701-754 = 九剑(湛卢~承影)同名梯子缺星段: 701+(剑序-2)*6+槽位,
#           槽位0=2★/1..5=6★~10★(3/4/5★复用月赛段661-690;轩辕全线在691-699)。
# 661+在客户端是DB档驱动的扩槽(r.grp模式内存重建,tools/gen_thingext.py生成),与服务端同口径。
SWORD_IDS = tuple(range(631, 641))
SWORD_STAR_BASE = 661          # 星级版起始
XY_STAR_BASE = 691             # 轩辕收集线2★起始
XY_MAX_STAR = 10
MAT_ID = 700                   # 名剑精魄(通用材料)
LADDER_BASE, LADDER_END = 701, 754   # 同名梯子段(九剑2★与6-10★)
XY_FEED_COST = 2               # 精魄升星消耗(每+1★,任意名剑;比直合贵,合成是主路线;占位待调)
TOWER_TF_FLOORS = (100, 500, 1000, 1500, 2000)   # 天关账号天赋里程碑层数
TOWER_TF_BASE = 9500           # 对应天赋ID 9500-9504(客户端按ID段判入账号天赋层)


def sword_star_id(sword_iid, star):
    """名剑月赛星级版物品ID(5/4/3★)。"""
    return SWORD_STAR_BASE + (sword_iid - 631) * 3 + (5 - star)


def xy_star_id(star):
    """轩辕剑收集线物品ID(1★=631,2★~10★=691+)。"""
    return 631 if star <= 1 else XY_STAR_BASE + star - 2


def xy_star_of(iid):
    """轩辕收集线物品ID→星级(非收集线ID返回0)。"""
    if iid == 631:
        return 1
    if XY_STAR_BASE <= iid <= XY_STAR_BASE + XY_MAX_STAR - 2:
        return iid - XY_STAR_BASE + 2
    return 0


def sword_k_of(iid):
    """任意名剑ID→剑序1-10(轩辕=1…承影=10;精魄700/非名剑=0)。全段覆盖:
    基础1★/月赛661-690/收集线691-699/同名梯子701-754。"""
    if 631 <= iid <= 640:
        return iid - 630
    if SWORD_STAR_BASE <= iid <= 690:
        return (iid - SWORD_STAR_BASE) // 3 + 1
    if XY_STAR_BASE <= iid <= 699:
        return 1
    if LADDER_BASE <= iid <= LADDER_END:
        return (iid - LADDER_BASE) // 6 + 2
    return 0


def ladder_star_id(k, star):
    """剑序+星级→名剑物品ID(全段):1★=基础剑;轩辕(剑序1)2-10★=收集线691-699;
    其余3-5★=月赛段661-690;2★与6-10★=同名梯子701+。与客户端 swordLadderId 同口径。"""
    star = max(1, min(int(star), XY_MAX_STAR))
    if star <= 1:
        return 630 + k
    if k == 1:
        return xy_star_id(star)
    if 3 <= star <= 5:
        return SWORD_STAR_BASE + (k - 1) * 3 + (5 - star)
    return LADDER_BASE + (k - 2) * 6 + (0 if star == 2 else star - 5)
PVP_ONLINE_TTL = 40            # 在线心跳过期秒数(旧客户端无坐标)
PVP_ONLINE_TTL_POS = 6         # 带坐标心跳过期秒数(同屏小人:离开场景约5秒后从他人画面消失)
_PVP_ONLINE = {}               # code -> dict(在线条目含位置/形象/战绩);进程内即可(重启清零无妨)
_pvp_online_lock = threading.Lock()

RATE_IP = (int(os.environ.get("CLOUDSAVE_RATE_IP") or 120), 60.0)  # 每 IP: 60 秒 120 次(本地全量压测可调高)
RATE_CODE = (60, 60.0)         # 每云码: 60 秒 60 次
RATE_REG = (30, 600.0)         # 每 IP: 10 分钟 30 次注册(ESA 回源共享边缘 IP,须放宽)
RATE_PVP = (int(os.environ.get("CLOUDSAVE_RATE_PVP") or 600), 60.0)  # presence 每 IP(豁免共享 IP 桶后自带;≈15个新客户端并发)
RATE_PVP_CODE = (90, 60.0)     # presence 每云码(新客户端 1.5s 心跳=40 次/分,2 倍余量)

USER_RE = re.compile(r"^[\w\-]{2,16}$", re.UNICODE)  # \w 含中文/字母/数字/下划线
PASS_MIN, PASS_MAX = 4, 64
PW_ITERS = 60000
LOGIN_FAIL_MAX = 8             # 连错锁定阈值
LOCK_SECONDS = 900             # 锁 15 分钟

_db_lock = threading.Lock()    # 串行化写操作, WAL 下读不受阻
_rate_lock = threading.Lock()
_rate = {}                     # key -> [tokens, last_ts]


def now():
    return int(time.time())


def day_cn(ts):
    """北京时区自然日编号(每日计分/发令牌上限的日界)。"""
    return (ts + 8 * 3600) // 86400


def week_cn(ts):
    """北京时区周编号(周一为界;day_cn 同源的 day→week 换算)。"""
    return (day_cn(ts) + 3) // 7


def week_day_range(w):
    """周编号→覆盖的 day_cn 区间[起,止](含端点)。"""
    return w * 7 - 3, w * 7 + 3


def month_cn(ts):
    """北京时区自然月编号(1970-01=0;月赛指定名剑按此轮换)。"""
    d = time.gmtime(ts + 8 * 3600)
    return d.tm_year * 12 + d.tm_mon - 1


def month_sword_iid(m):
    """月编号→当月指定名剑基础ID(631-640 顺序轮换,十个月一轮)。"""
    return 631 + (m % 10)


def elo_k(games):
    """K 系数: 新手涨得快,老手趋于稳定。"""
    return 32 if games < 10 else (24 if games < 30 else 16)


def elo_update(ra, rb, ka, kb, win):
    """ELO 双边结算。win=1 表示 a 胜。返回 (a新分, b新分, a增量)。"""
    ea = 1.0 / (1.0 + 10.0 ** ((rb - ra) / 400.0))
    na = max(ELO_FLOOR, int(round(ra + ka * ((1 if win else 0) - ea))))
    nb = max(ELO_FLOOR, int(round(rb + kb * ((0 if win else 1) - (1.0 - ea)))))
    return na, nb, na - ra


# ---- 账号物品仓库 / 发放台账 / 周月懒结算 ----

def acc_add(conn, code, iid, n, ts):
    """物品入账号仓库(可叠加以池内现有数量累加)。"""
    conn.execute(
        """INSERT INTO acc_item(code,iid,n,ts) VALUES(?,?,?,?)
           ON CONFLICT(code,iid) DO UPDATE SET n=n+excluded.n, ts=excluded.ts""",
        (code, iid, n, ts))


def grant_xy(conn, code, ts):
    """[已废弃2026-09-03]旧"每得一把+1★"机制被星级相加合成取代;
    保留仅供旧台账口径参照,新代码勿调(购买/月榜走 xy_grant_reward)。"""
    star = conn.execute(
        "SELECT MAX(amt) m FROM pvp_award WHERE code=? AND period='xy'",
        (code,)).fetchone()["m"] or 0
    for r in conn.execute(
            "SELECT iid FROM acc_item WHERE code=? AND (iid=631 OR iid BETWEEN 691 AND 699)",
            (code,)).fetchall():
        star = max(star, xy_star_of(r["iid"]))
    new = 1 if star == 0 else min(star + 1, XY_MAX_STAR)
    conn.execute(
        "DELETE FROM acc_item WHERE code=? AND (iid=631 OR iid BETWEEN 691 AND 699)",
        (code,))
    conn.execute("INSERT INTO acc_item(code,iid,n,ts) VALUES(?,?,1,?)",
                 (code, xy_star_id(new), ts))
    conn.execute(
        """INSERT INTO pvp_award(code,period,kind,ts,amt,detail) VALUES(?,'xy','xy',?,?,?)
           ON CONFLICT(code,period,kind) DO UPDATE SET ts=excluded.ts, amt=excluded.amt,
           detail=excluded.detail""",
        (code, ts, new, "轩辕剑收集线%d★" % new))
    return new


def sword_star_of(iid):
    """任意名剑ID→星级:基础631-640=1★;月赛661-690=5-((i-661)%3);
    收集线691-699走xy_star_of;梯子701-754=槽位0为2★,1..5为6-10★;
    精魄700/非名剑=0。"""
    if 631 <= iid <= 640:
        return 1
    if 661 <= iid <= 690:
        return 5 - (iid - SWORD_STAR_BASE) % 3
    if LADDER_BASE <= iid <= LADDER_END:
        j = (iid - LADDER_BASE) % 6
        return 2 if j == 0 else j + 5
    return xy_star_of(iid)


def _pool_line_star(conn, code):
    """池内收集线剑(691-699)当前最高星。"""
    s = 0
    for r in conn.execute(
            "SELECT iid FROM acc_item WHERE code=? AND iid BETWEEN 691 AND 699",
            (code,)).fetchall():
        s = max(s, xy_star_of(r["iid"]))
    return s


def xy_ref_star(conn, code):
    """收集线参照星级=台账最高与池内收集线剑取最大(单机档里的轩辕也覆盖:
    它入池时台账已记等星,防身持高星剑时低星合成/喂魄白耗材料)。"""
    star = conn.execute(
        "SELECT MAX(amt) m FROM pvp_award WHERE code=? AND period='xy'",
        (code,)).fetchone()["m"] or 0
    return max(star, _pool_line_star(conn, code))


def xy_grant(conn, code, star, ts):
    """收集线落位到star★:池内691-699清空只留新剑一把;台账upsert记历史
    最高星(period='xy',取出不亏口径)。631(1★)是普通材料剑,不在此清。"""
    conn.execute(
        "DELETE FROM acc_item WHERE code=? AND iid BETWEEN 691 AND 699",
        (code,))
    conn.execute("INSERT INTO acc_item(code,iid,n,ts) VALUES(?,?,1,?)",
                 (code, xy_star_id(star), ts))
    conn.execute(
        """INSERT INTO pvp_award(code,period,kind,ts,amt,detail) VALUES(?,'xy','xy',?,?,?)
           ON CONFLICT(code,period,kind) DO UPDATE SET ts=excluded.ts,
           amt=MAX(pvp_award.amt,excluded.amt),detail=excluded.detail""",
        (code, ts, star, "轩辕剑收集线%d★" % star))
    return star


def _pool_sword_star(conn, code, k):
    """池内剑k(星≥2条目)的最高星——月赛段+梯子段。非轩辕同名合成的
    "结果须提升"参照(无台账口径:取出后重合同星合法,材料是真消耗)。"""
    best = 0
    for r in conn.execute(
            "SELECT iid FROM acc_item WHERE code=? "
            "AND (iid BETWEEN 661 AND 699 OR iid BETWEEN ? AND ?)",
            (code, LADDER_BASE, LADDER_END)).fetchall():
        iid = r["iid"]
        if sword_k_of(iid) == k:
            best = max(best, sword_star_of(iid))
    return best


def forge_xy(conn, code, i1, i2, ts):
    """名剑合成(2026-09-03同名梯子改版:星级相加)。
    - 同名+同名(非轩辕):两把该剑熔成该剑高星,s1+s2封顶10★,结果走梯子/月赛段;
      结果须高于池内该剑最高星(防白耗材料)。
    - 轩辕+轩辕/混名:熔成轩辕收集线(691-699池内只留一把;台账记历史最高星,
      取出不亏);结果须高于收集线参照星;收集线剑不在池(在单机档)时拒绝,
      防身持旧星剑又池养新星剑的双份漏。
    已满星(10★)名剑不可为材料。返回 (新iid,新星,None)/(None,0,错误文案)。"""
    k1, s1 = sword_k_of(i1), sword_star_of(i1)
    k2, s2 = sword_k_of(i2), sword_star_of(i2)
    if k1 <= 0 or k2 <= 0 or s1 <= 0 or s2 <= 0:
        return None, 0, "只能以十大名剑为材料"
    if s1 >= XY_MAX_STAR or s2 >= XY_MAX_STAR:
        return None, 0, "已满星(%d★)名剑不可为材料" % XY_MAX_STAR
    same = (k1 == k2 and k1 > 1)
    new = min(s1 + s2, XY_MAX_STAR)
    if same:
        best = _pool_sword_star(conn, code, k1)
        if new <= best:
            return None, 0, "%s已是%d★,此合成无提升" % (sword_name(630 + k1), best)
    else:
        ref, pool_ref = xy_ref_star(conn, code), _pool_line_star(conn, code)
        if ref > pool_ref:
            return None, 0, "轩辕收集线名剑不在仓库(可能在单机档),通关回仓后再来"
        if new <= ref:
            return None, 0, "收集线已是%d★,此合成无提升" % ref
    need = {i1: 2} if i1 == i2 else {i1: 1, i2: 1}
    for iid, cnt in need.items():
        row = conn.execute("SELECT n FROM acc_item WHERE code=? AND iid=?",
                           (code, iid)).fetchone()
        if row is None or row["n"] < cnt:
            return None, 0, "仓库中%s不足(需%d把)" % (sword_name(iid), cnt)
    for iid in (i1, i2):
        conn.execute("UPDATE acc_item SET n=n-1 WHERE code=? AND iid=?",
                     (code, iid))
    conn.execute("DELETE FROM acc_item WHERE code=? AND n<=0", (code,))
    if same:
        res_iid = ladder_star_id(k1, new)
        acc_add(conn, code, res_iid, 1, ts)
        return res_iid, new, None
    xy_grant(conn, code, new, ts)
    return xy_star_id(new), new, None


def _feed_take(conn, code):
    """精魄扣XY_FEED_COST枚。返回错误文案(None=成功)。"""
    row = conn.execute("SELECT n FROM acc_item WHERE code=? AND iid=?",
                       (code, MAT_ID)).fetchone()
    have = row["n"] if row else 0
    if have < XY_FEED_COST:
        return "名剑精魄不足(需%d枚,仓库有%d枚)" % (XY_FEED_COST, have)
    conn.execute("UPDATE acc_item SET n=n-? WHERE code=? AND iid=?",
                 (XY_FEED_COST, code, MAT_ID))
    conn.execute("DELETE FROM acc_item WHERE code=? AND iid=? AND n<=0",
                 (code, MAT_ID))
    return None


def feed_xy(conn, code, iid, ts):
    """精魄升星(2026-09-03改版:可喂任意名剑),每耗XY_FEED_COST枚。
    - iid=0/收集线剑(691-699)/轩辕1★:喂轩辕收集线+1★(台账口径不变,取出不亏);
    - 其余名剑星级剑(星≥2):吃掉池中该剑1把换+1★,封顶10★(无台账:取出重合合法)。
    已满星/剑不在池/精魄不足都会拒。返回 (新iid,新星,None)/(None,0,错误文案)。"""
    if iid and sword_k_of(iid) == 1:
        iid = 0   # 轩辕系统一走收集线口径
    if iid == 0:
        ref, pool_ref = xy_ref_star(conn, code), _pool_line_star(conn, code)
        if ref <= 0:
            return None, 0, "还没有轩辕收集线,先合成两把轩辕(或商店买轩辕)"
        if ref > pool_ref:
            return None, 0, "轩辕收集线名剑不在仓库(可能在单机档),通关回仓后再来"
        if ref >= XY_MAX_STAR:
            return None, 0, "轩辕收集线已满星(%d★)" % XY_MAX_STAR
        ferr = _feed_take(conn, code)
        if ferr:
            return None, 0, ferr
        xy_grant(conn, code, ref + 1, ts)
        return xy_star_id(ref + 1), ref + 1, None
    k, s = sword_k_of(iid), sword_star_of(iid)
    if k <= 0 or s < 2:
        return None, 0, "只能喂星级名剑(≥2★);1★基础剑是合成材料"
    if s >= XY_MAX_STAR:
        return None, 0, "%s已满星(%d★)" % (sword_name(iid), XY_MAX_STAR)
    row = conn.execute("SELECT n FROM acc_item WHERE code=? AND iid=?",
                       (code, iid)).fetchone()
    if row is None or row["n"] < 1:
        return None, 0, "%s不在仓库(可能在单机档),通关回仓后再来" % sword_name(iid)
    ferr = _feed_take(conn, code)
    if ferr:
        return None, 0, ferr
    conn.execute("UPDATE acc_item SET n=n-1 WHERE code=? AND iid=?",
                 (code, iid))
    conn.execute("DELETE FROM acc_item WHERE code=? AND iid=? AND n<=0",
                 (code, iid))
    res_iid = ladder_star_id(k, s + 1)
    acc_add(conn, code, res_iid, 1, ts)
    return res_iid, s + 1, None


def xy_grant_reward(conn, code, ts):
    """月榜/商店入一把轩辕:收集线未满星→发1★轩辕剑(631,合成材料);
    已满星→折算名剑精魄×1(额外所得不浪费,2026-09-03用户拍板)。
    返回(发放iid,数量)。"""
    if xy_ref_star(conn, code) >= XY_MAX_STAR:
        acc_add(conn, code, MAT_ID, 1, ts)
        return MAT_ID, 1
    acc_add(conn, code, 631, 1, ts)
    return 631, 1


def award_once(conn, code, period, kind, ts, amt=0, detail=""):
    """幂等发放:首次写入台账返回 True(奖励动作只在 True 时执行),重复返回 False。"""
    cur = conn.execute(
        "INSERT OR IGNORE INTO pvp_award(code,period,kind,ts,amt,detail) VALUES(?,?,?,?,?,?)",
        (code, period, kind, ts, amt, detail))
    return cur.rowcount == 1


def _add_coins(conn, code, amt, ts):
    """论剑币入账(无行先建)。"""
    conn.execute("INSERT OR IGNORE INTO pvp_player(code,pname,title,coin,ts) "
                 "VALUES(?,'','',0,?)", (code, ts))
    conn.execute("UPDATE pvp_player SET coin=coin+?,ts=? WHERE code=?",
                 (amt, ts, code))


def _elo_board(conn, limit):
    """ELO 榜(上榜门槛:计分局数),返回 [(code, score)] 按分desc/达成先出asc。"""
    return [(r["code"], r["score"]) for r in conn.execute(
        "SELECT code,score FROM pvp_rating WHERE games>=? "
        "ORDER BY score DESC, ts ASC LIMIT ?", (PVP_BOARD_MIN_GAMES, limit)).fetchall()]


def pvp_settle(conn, ts):
    """周/月懒结算:新周期内首次请求时,用"周期末快照"结算刚结束的上一周期。
    - 首次部署(无游标):只落游标不回溯结算(历史周期数据不齐,不做追溯)。
    - 周: 个人真人计分胜场阶梯(5/10/20→100/150/250币) + ELO榜前十称号「剑台十杰」(替换旧持有者);
    - 月: 指定名剑(月编号轮换631-640) 冠军5★/亚军4★/季军3★入库 + 4~10名轩辕剑收集线+1★。
    全程幂等(pvp_award 台账),调用方须已持有 _db_lock。"""
    wk, mo = week_cn(ts), month_cn(ts)
    rows = {r["key"]: r["val"] for r in conn.execute(
        "SELECT key,val FROM pvp_meta WHERE key IN ('week','month')").fetchall()}

    # ---- 周结算 ----
    if "week" not in rows:
        conn.execute("INSERT OR REPLACE INTO pvp_meta(key,val,ts) VALUES('week',?,?)",
                     (wk, ts))
    elif wk > rows["week"]:
        last = rows["week"]
        d0, d1 = week_day_range(last)
        period = "w%d" % last
        # 1) 个人胜场阶梯:该周真人计分胜场(计数含 tier 达标即发,bots 排除)
        for r in conn.execute(
                "SELECT atk code, COUNT(*) c FROM pvp_match "
                "WHERE day BETWEEN ? AND ? AND counted=1 AND win=1 AND bot=0 "
                "GROUP BY atk", (d0, d1)).fetchall():
            for w, coin in PVP_WEEK_TIERS:
                if r["c"] >= w and award_once(conn, r["code"], period, "w%d" % w,
                                              ts, coin, "周%d胜" % w):
                    _add_coins(conn, r["code"], coin, ts)
        # 2) ELO 榜前十称号:先清旧持有者再授新(榜外/未上榜自动摘除)
        top = [c for c, _ in _elo_board(conn, 10)]
        conn.execute("UPDATE pvp_player SET title='' WHERE title=?",
                     (PVP_WEEK_TOP_TITLE,))
        for c in top:
            conn.execute(
                "INSERT INTO pvp_player(code,pname,title,coin,ts) VALUES(?,'',?,0,?) "
                "ON CONFLICT(code) DO UPDATE SET title=excluded.title",
                (c, PVP_WEEK_TOP_TITLE, ts))
            award_once(conn, c, period, "wtop", ts, 0, "周榜前十")
        conn.execute("UPDATE pvp_meta SET val=?,ts=? WHERE key='week'", (wk, ts))

    # ---- 月结算 ----
    if "month" not in rows:
        conn.execute("INSERT OR REPLACE INTO pvp_meta(key,val,ts) VALUES('month',?,?)",
                     (mo, ts))
    elif mo > rows["month"]:
        last = rows["month"]
        period = "m%d" % last
        sword = month_sword_iid(last)
        top = _elo_board(conn, 10)
        for rank, (c, _) in enumerate(top, 1):
            if rank <= 3:
                star = 4 if rank == 2 else (3 if rank == 3 else 5)
                if award_once(conn, c, period, "m%d" % rank, ts, 0,
                              "月榜第%d名·%d★%s" % (rank, star, sword_name(sword))):
                    acc_add(conn, c, sword_star_id(sword, star), 1, ts)
            elif award_once(conn, c, period, "m%d" % rank, ts, 0,
                            "月榜第%d名·轩辕剑" % rank):
                # 2026-09-03改版:不再自动+1★,直发1★轩辕剑(合成材料);
                # 收集线已满星则折算名剑精魄(额外所得不浪费)
                xy_grant_reward(conn, c, ts)
        conn.execute("UPDATE pvp_meta SET val=?,ts=? WHERE key='month'", (mo, ts))


def sword_name(iid):
    """名剑ID→显示名(含月赛/收集线/梯子星级版;用于战报与错误文案)。"""
    _NAMES = ("轩辕剑", "湛卢剑", "赤霄剑", "太阿剑", "龙渊剑",
              "干将剑", "莫邪剑", "鱼肠剑", "纯钧剑", "承影剑")
    if iid == MAT_ID:
        return "名剑精魄"
    k, s = sword_k_of(iid), sword_star_of(iid)
    if k <= 0:
        return "物品%d" % iid
    return "%s(%d星)" % (_NAMES[k - 1], s) if s > 1 else _NAMES[k - 1]


def db():
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    return conn


def init_db():
    os.makedirs(BLOB_DIR, exist_ok=True)
    conn = db()
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS code(
          code TEXT PRIMARY KEY, name TEXT DEFAULT '',
          created_at INTEGER, last_seen INTEGER, banned INTEGER DEFAULT 0);
        CREATE TABLE IF NOT EXISTS slot(
          code TEXT, slot INTEGER, ver INTEGER, ts INTEGER, size INTEGER,
          md5 TEXT, name TEXT, chain INTEGER DEFAULT 0, ver_game INTEGER DEFAULT 0,
          PRIMARY KEY(code, slot, ver));
        CREATE TABLE IF NOT EXISTS profile(
          code TEXT, fname TEXT, ts INTEGER, size INTEGER, md5 TEXT,
          PRIMARY KEY(code, fname));
        CREATE TABLE IF NOT EXISTS account(
          user TEXT PRIMARY KEY, salt TEXT, pwhash TEXT, code TEXT UNIQUE,
          created_at INTEGER, last_seen INTEGER,
          fails INTEGER DEFAULT 0, lock_until REAL DEFAULT 0);
        CREATE TABLE IF NOT EXISTS invite(
          code TEXT PRIMARY KEY, note TEXT DEFAULT '',
          used_by TEXT, used_at INTEGER, created_at INTEGER);
        CREATE TABLE IF NOT EXISTS tower(
          code TEXT PRIMARY KEY, floor INTEGER, name TEXT DEFAULT '', ts INTEGER);
        CREATE TABLE IF NOT EXISTS flags(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          code TEXT, kind TEXT, detail TEXT, ts INTEGER);
        CREATE TABLE IF NOT EXISTS pvp_snap(      -- 玩家对战镜像(一账号一份)
          code TEXT PRIMARY KEY, pid TEXT UNIQUE, -- pid=对外短标识,榜单/挑战用它,不暴露云码
          name TEXT DEFAULT '', n INTEGER DEFAULT 1,
          pw INTEGER DEFAULT 0, pw2 INTEGER DEFAULT 0,
          size INTEGER, md5 TEXT, ver INTEGER DEFAULT 1, ts INTEGER);
        CREATE TABLE IF NOT EXISTS pvp_rating(    -- 论剑台积分(ELO)
          code TEXT PRIMARY KEY, score INTEGER DEFAULT 1000,
          wins INTEGER DEFAULT 0, losses INTEGER DEFAULT 0,
          games INTEGER DEFAULT 0, ts INTEGER);
        CREATE TABLE IF NOT EXISTS pvp_tok(       -- 挑战令牌: 一次下载一令牌一计分
          tok TEXT PRIMARY KEY, atk TEXT, def TEXT,
          day INTEGER, used INTEGER DEFAULT 0, ts INTEGER);
        CREATE TABLE IF NOT EXISTS pvp_match(     -- 对局流水(审计/每日上限判定/二期实时预留)
          id INTEGER PRIMARY KEY AUTOINCREMENT, ts INTEGER, day INTEGER,
          atk TEXT, def TEXT, mode INTEGER, win INTEGER, tok TEXT,
          ra INTEGER, rb INTEGER, da INTEGER, db INTEGER, counted INTEGER);
        CREATE TABLE IF NOT EXISTS pvp_player(    -- 论剑台玩家资料:玩家名/称号/论剑币
          code TEXT PRIMARY KEY, pname TEXT,
          title TEXT DEFAULT '', coin INTEGER DEFAULT 0, ts INTEGER);
        CREATE TABLE IF NOT EXISTS pvp_buy(       -- 商店购买流水(once 类据此判重)
          code TEXT, item TEXT, ts INTEGER);
        CREATE TABLE IF NOT EXISTS gift_tf(       -- 账号赠礼天赋(hello 带回,客户端幂等领取)
          code TEXT, tf INTEGER, ts INTEGER, note TEXT DEFAULT '',
          PRIMARY KEY(code, tf));
        CREATE TABLE IF NOT EXISTS acc_item(      -- 账号物品仓库(论剑台NPC存取;出图即离池)
          code TEXT, iid INTEGER, n INTEGER, ts INTEGER,
          PRIMARY KEY(code, iid));
        CREATE TABLE IF NOT EXISTS acc_sess(      -- 仓库进图会话(服务端权威held;断线重进回滚)
          code TEXT PRIMARY KEY, held TEXT, ts INTEGER);
        CREATE TABLE IF NOT EXISTS acc_dep(       -- 名剑/精魄出图(exit)与回存(dep)流水
          code TEXT, iid INTEGER, kind TEXT,      -- (dep可用额度=exit-dep,封读档复制路)
          amt INTEGER, ts INTEGER);
        CREATE TABLE IF NOT EXISTS pvp_award(     -- 日/周/月/成就发放台账(幂等+战报来源)
          code TEXT, period TEXT, kind TEXT, ts INTEGER,
          amt INTEGER DEFAULT 0, detail TEXT DEFAULT '',
          PRIMARY KEY(code, period, kind));
        CREATE TABLE IF NOT EXISTS pvp_meta(      -- 周/月结算游标(懒触发:新周期首请求结算上期)
          key TEXT PRIMARY KEY, val INTEGER, ts INTEGER);
        CREATE TABLE IF NOT EXISTS sess(         -- 挤号: 登录会话令牌(新登录顶掉旧sid)
          code TEXT PRIMARY KEY, sid TEXT, ts INTEGER);
        CREATE TABLE IF NOT EXISTS party(        -- 组队:一队一行,队长唯一(队长制)
          id INTEGER PRIMARY KEY AUTOINCREMENT, leader TEXT UNIQUE, ts INTEGER);
        CREATE TABLE IF NOT EXISTS party_member( -- 队员(一人至多一队,UNIQUE索引保证)
          party_id INTEGER, code TEXT, ts INTEGER, PRIMARY KEY(party_id, code));
        CREATE TABLE IF NOT EXISTS party_invite( -- 邀请(收件人+发起人唯一;600s 过期惰性清)
          to_code TEXT, from_code TEXT, party_id INTEGER, ts INTEGER,
          PRIMARY KEY(to_code, from_code));
        """
    )
    # 一人至多一队:老库补建唯一索引(新库 CREATE 时若无索引也走这条)
    try:
        conn.execute(
            "CREATE UNIQUE INDEX IF NOT EXISTS idx_party_member_code ON party_member(code)")
    except Exception:
        pass  # 索引已存在
    # 已有库的列迁移(CREATE IF NOT EXISTS 不会给旧表加列)
    for col in ("tp", "td"):
        try:
            conn.execute("ALTER TABLE slot ADD COLUMN %s INTEGER DEFAULT 0" % col)
        except Exception:
            pass  # 列已存在
    # 名宿镜像标记:bot=1(可被挑战、挑战者计分,自身分数/games 冻结→永不占榜位)。
    # 运营方直接 SQL 设置,上传端点不收 bot 参数(零攻击面)。
    try:
        conn.execute("ALTER TABLE pvp_snap ADD COLUMN bot INTEGER DEFAULT 0")
    except Exception:
        pass  # 列已存在
    # 匹配挑战:令牌携带槽位奖励(1/2/3币,0=非匹配挑战走老逻辑30/15)
    try:
        conn.execute("ALTER TABLE pvp_tok ADD COLUMN reward INTEGER DEFAULT 0")
    except Exception:
        pass  # 列已存在
    # 对局流水补记 bot 标记(日/周阶梯只计真人计分局)
    try:
        conn.execute("ALTER TABLE pvp_match ADD COLUMN bot INTEGER DEFAULT 0")
    except Exception:
        pass  # 列已存在
    conn.commit()
    conn.close()


def rate_allow(key, cap, per):
    ts = time.time()
    with _rate_lock:
        st = _rate.get(key)
        if st is None:
            _rate[key] = [float(cap), ts]
            st = _rate[key]
        elapsed = ts - st[1]
        st[0] = min(float(cap), st[0] + elapsed * (cap / per))
        st[1] = ts
        if st[0] >= 1.0:
            st[0] -= 1.0
            if len(_rate) > 20000:  # 防内存膨胀: 粗暴清理过期桶
                dead = [k for k, v in _rate.items() if ts - v[1] > per * 4]
                for k in dead:
                    _rate.pop(k, None)
            return True
        return False


def gen_code(conn):
    while True:
        c = "".join(secrets.choice(CODE_CHARS) for _ in range(12))
        if not conn.execute("SELECT 1 FROM code WHERE code=?", (c,)).fetchone():
            return c


def norm_code(raw):
    if not raw:
        return None
    c = raw.strip().upper().replace("-", "")
    return c if CODE_RE.match(c) else None


def norm_invite(raw):
    if not raw:
        return None
    c = str(raw).strip().upper().replace("-", "").replace(" ", "")
    return c if INVITE_RE.match(c) else None


def gen_invite(conn, n=1, note=""):
    """批量生成未占用的邀请码(发码方=作者,经 mkinvite.py 或直接调用)。"""
    out = []
    while len(out) < n:
        c = "".join(secrets.choice(INVITE_CHARS) for _ in range(8))
        if conn.execute("SELECT 1 FROM invite WHERE code=?", (c,)).fetchone():
            continue
        conn.execute("INSERT INTO invite(code,note,created_at) VALUES(?,?,?)",
                     (c, note, now()))
        out.append(c)
    conn.commit()
    return out


def hash_pw(password, salt_hex):
    return hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), bytes.fromhex(salt_hex), PW_ITERS).hex()


def blob_path(code, name):
    return os.path.join(BLOB_DIR, code, name)


def write_blob(code, name, data):
    path = blob_path(code, name)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "wb") as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


# ================= 组队(论剑台):party/party_member/party_invite =================
PARTY_MAX = 4            # 队伍上限(为组队挑战任务预留)
PARTY_INVITE_TTL = 600   # 邀请有效期(秒)


def _party_of(conn, code):
    """code 所在队伍 → party 行 或 None"""
    r = conn.execute(
        """SELECT p.* FROM party p JOIN party_member m ON m.party_id=p.id
           WHERE m.code=?""", (code,)).fetchone()
    return r


def _party_info(conn, code, online_codes=None):
    """code 的队伍详情(None=不在队):成员含名字/镜像pid/在线标记"""
    p = _party_of(conn, code)
    if p is None:
        return None
    members = []
    for m in conn.execute(
            "SELECT code FROM party_member WHERE party_id=? ORDER BY ts, code",
            (p["id"],)).fetchall():
        c = m["code"]
        prow = conn.execute(
            "SELECT pname,title FROM pvp_player WHERE code=?", (c,)).fetchone()
        srow = conn.execute(
            "SELECT pid,name FROM pvp_snap WHERE code=?", (c,)).fetchone()
        nm = (prow["pname"] if prow and prow["pname"] else
              (srow["name"] if srow else "")) or "无名侠客"
        members.append({
            "code": c, "name": nm,
            "pid": srow["pid"] if srow else None,
            "title": prow["title"] if prow else "",
            "leader": 1 if c == p["leader"] else 0,
            "online": 1 if (online_codes and c in online_codes) else 0})
    return {"id": p["id"], "leader": p["leader"], "members": members}


def _resolve_target(conn, q):
    """邀请目标解析:pid(镜像id)优先,其次 name(侠名),再次 code(云码)。→code 或 None"""
    pid = (q.get("pid") or "").strip()
    if pid:
        r = conn.execute("SELECT code FROM pvp_snap WHERE pid=?", (pid,)).fetchone()
        if r:
            return r["code"]
    name = (q.get("name") or "").strip()
    if name:
        r = conn.execute(
            """SELECT m.code FROM pvp_player m LEFT JOIN pvp_snap s ON s.code=m.code
               WHERE m.pname=? OR s.name=? ORDER BY m.ts DESC LIMIT 1""",
            (name, name)).fetchone()
        if r:
            return r["code"]
    # 注意:query() 对重名参数取首个——?code=调用方&...&code=目标 恒取到调用方,
    # 目标云码必须走独立参数名 target
    tc = norm_code(q.get("target") or "")
    if tc:
        r = conn.execute("SELECT code FROM code WHERE code=?", (tc,)).fetchone()
        if r:
            return tc
    return None


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "jscloud/1.0"

    # ---------- 基础设施 ----------
    def log_message(self, fmt, *args):
        pass  # 静默; 访问日志交给 nginx

    def client_ip(self):
        # nginx 会带 X-Real-IP (ESA 回源时为边缘 IP); 不信其它来源——本服务只监听 127.0.0.1
        return self.headers.get("X-Real-IP") or self.client_address[0]

    def send_json(self, obj, status=200):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def send_blob(self, data, md5, status=200):
        self.send_response(status)
        self.send_header("Content-Type", "application/octet-stream")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Md5", md5)
        self.end_headers()
        self.wfile.write(data)

    def err(self, code, msg, status=200):
        self.send_json({"code": code, "msg": msg, "data": None}, status)

    def read_body(self, cap):
        n = int(self.headers.get("Content-Length") or 0)
        if n <= 0:
            return b""
        if n > cap:
            self.err(4, "body too large", 413)
            return None
        return self.rfile.read(n)

    def query(self):
        q = parse_qs(urlparse(self.path).query)
        return {k: v[0] for k, v in q.items()}

    # ---------- 端点 ----------
    def do_GET(self):
        try:
            u = urlparse(self.path)
            if u.path == "/api/save/ping":
                self.send_json({"code": 0, "msg": "ok", "data": {"t": now()}})
                return
            if not self.check_rate():
                return
            q = self.query()
            if u.path == "/api/save/slot":
                self.get_slot(q)
                return
            if u.path == "/api/save/profile":
                self.get_profile(q)
                return
            if u.path == "/api/save/tower":
                self.get_tower(q)
                return
            if u.path == "/api/save/pvp/board":
                self.get_pvp_board(q)
                return
            if u.path == "/api/save/pvp/match":
                self.get_pvp_match(q)
                return
            if u.path == "/api/save/pvp/me":
                self.get_pvp_me(q)
                return
            if u.path == "/api/save/pvp/shop":
                self.get_pvp_shop(q)
                return
            if u.path == "/api/save/pvp/store":
                self.get_pvp_store(q)
                return
            if u.path == "/api/save/pvp/snap":
                self.get_pvp_snap(q)
                return
            if u.path == "/api/save/pvp/challenge":
                self.get_pvp_challenge(q)
                return
            self.err(404, "not found", 404)
        except BrokenPipeError:
            pass
        except Exception as e:  # noqa: BLE001
            try:
                self.err(500, "server error: %s" % e, 500)
            except Exception:
                pass

    def do_POST(self):
        try:
            u = urlparse(self.path)
            if u.path == "/api/save/pvp/presence":
                # 心跳豁免共享 IP 桶(ESA 回源共享边缘 IP,1.5s 心跳会打爆 120/分);
                # 函数内自带 presence 专属双桶。照 do_GET ping 豁免先例。
                self.post_pvp_presence(self.query())
                return  # 缺此行会穿透 check_rate(白耗 IP 桶)并落到末尾 404 双写响应
            if u.path == "/api/save/pvp/party":
                # 组队操作(低频;复用 check_code 鉴权,不占 presence 心跳限流桶)
                self.post_pvp_party(self.query())
                return
            if not self.check_rate():
                return
            q = self.query()
            if u.path == "/api/save/hello":
                self.post_hello()
                return
            if u.path == "/api/save/register":
                self.post_register()
                return
            if u.path == "/api/save/login":
                self.post_login()
                return
            if u.path == "/api/save/slot":
                self.post_slot(q)
                return
            if u.path == "/api/save/profile":
                self.post_profile(q)
                return
            if u.path == "/api/save/tower":
                self.post_tower(q)
                return
            if u.path == "/api/save/pvp/snap":
                self.post_pvp_snap(q)
                return
            if u.path == "/api/save/pvp/report":
                self.post_pvp_report(q)
                return
            if u.path == "/api/save/pvp/name":
                self.post_pvp_name(q)
                return
            if u.path == "/api/save/pvp/buy":
                self.post_pvp_buy(q)
                return
            if u.path == "/api/save/pvp/store":
                self.post_pvp_store(q)
                return
            if u.path == "/api/save/pvp/achclaim":
                self.post_pvp_achclaim(q)
                return
            if u.path == "/api/save/pvp/title":
                self.post_pvp_title(q)
                return
            self.err(404, "not found", 404)
        except BrokenPipeError:
            pass
        except Exception as e:  # noqa: BLE001
            try:
                self.err(500, "server error: %s" % e, 500)
            except Exception:
                pass

    def check_rate(self):
        ip = self.client_ip()
        if not rate_allow("ip:" + ip, *RATE_IP):
            self.err(9, "rate limited", 429)
            return False
        return True

    def check_code(self, q, create=False, name=None):
        """返回 (code 或 None). code 无效且 create=True 时新建。"""
        raw = q.get("code", "")
        code = norm_code(raw)
        conn = db()
        try:
            if code is None:
                if not create:
                    self.err(1, "bad code")
                    return None
                code = gen_code(conn)
                conn.execute(
                    "INSERT INTO code(code,name,created_at,last_seen) VALUES(?,?,?,?)",
                    (code, name or "", now(), now()))
                conn.commit()
                return code
            row = conn.execute("SELECT * FROM code WHERE code=?", (code,)).fetchone()
            if row is None:
                if create:
                    conn.execute(
                        "INSERT INTO code(code,name,created_at,last_seen) VALUES(?,?,?,?)",
                        (code, name or "", now(), now()))
                    conn.commit()
                    return code
                self.err(2, "code not found")
                return None
            if row["banned"]:
                self.err(3, "banned")
                return None
            # 挤号: 该云码已签发会话(新版客户端登录/注册时) → 请求必须带当前 sid,
            # 否则=已被别处登录顶掉。sid 恒在 query 串(hello/pvp-name 等 body 携带
            # code 的端点自组 dict,不依赖调用方传参,这里直读 self.query())。
            # 旧版客户端无 sess 行 → 永不触发(混跑期零破坏,随自动更新收敛)。
            srow = conn.execute("SELECT sid FROM sess WHERE code=?", (code,)).fetchone()
            if srow is not None and self.query().get("sid", "") != srow["sid"]:
                self.err(13, "账号已在别处登录,请重新登录")
                return None
            if name is not None:
                conn.execute("UPDATE code SET name=?,last_seen=? WHERE code=?",
                             (name, now(), code))
            else:
                conn.execute("UPDATE code SET last_seen=? WHERE code=?", (now(), code))
            conn.commit()
            return code
        finally:
            conn.close()

    # ---------- 账号 ----------
    def read_credentials(self):
        """register/login 公共入参: JSON body 优先, 空 body 落 query。回 (user,pass,invite) 或 None。"""
        body = self.read_body(4096)
        if body is None:
            return None
        payload = {}
        if body:
            try:
                payload = json.loads(body.decode("utf-8"))
            except Exception:
                self.err(5, "bad json")
                return None
        else:
            payload = dict(self.query())
        user = str(payload.get("user") or "").strip()
        pw = str(payload.get("pass") or "").strip()
        inv = norm_invite(payload.get("invite"))
        # v=2: 新版客户端(带挤号会话能力)。旧客户端不签发 sid → 混跑期互不干扰。
        v = payload.get("v")
        return user, pw, inv, v

    def post_register(self):
        if not rate_allow("reg:" + self.client_ip(), *RATE_REG):
            self.err(9, "注册过于频繁,请稍后再试", 429)
            return
        cred = self.read_credentials()
        if cred is None:
            return
        user, pw, inv = cred[0], cred[1], cred[2]  # (第4位是v,挤号用)
        if not USER_RE.match(user):
            self.err(10, "账号需为2~16位字母/数字/中文")
            return
        if not (PASS_MIN <= len(pw) <= PASS_MAX):
            self.err(10, "密码需为%d~%d位" % (PASS_MIN, PASS_MAX))
            return
        if inv is None:
            self.err(15, "注册需要邀请码(8位,向作者索取)")
            return
        salt = secrets.token_hex(16)
        pwhash = hash_pw(pw, salt)
        conn = db()
        try:
            with _db_lock:
                if conn.execute("SELECT 1 FROM account WHERE user=?", (user,)).fetchone():
                    self.err(11, "该账号已被注册")
                    return
                # 原子核销: UPDATE 带未用条件,并发同码注册只有一个成功
                cur = conn.execute(
                    "UPDATE invite SET used_by=?, used_at=? "
                    "WHERE code=? AND used_by IS NULL", (user, now(), inv))
                if cur.rowcount != 1:
                    conn.rollback()
                    self.err(15, "邀请码无效或已被使用")
                    return
                code = gen_code(conn)
                conn.execute(
                    "INSERT INTO code(code,name,created_at,last_seen) VALUES(?,?,?,?)",
                    (code, "", now(), now()))
                conn.execute(
                    "INSERT INTO account(user,salt,pwhash,code,created_at,last_seen) "
                    "VALUES(?,?,?,?,?,?)",
                    (user, salt, pwhash, code, now(), now()))
                # 挤号: 新版客户端注册即签发会话,该账号从此受单会话约束
                sid = None
                if str(cred[3]) == "2":
                    sid = secrets.token_hex(8)
                    conn.execute("INSERT OR REPLACE INTO sess(code,sid,ts) VALUES(?,?,?)",
                                 (code, sid, now()))
                conn.commit()
            data = {"user": user, "code": code}
            if sid:
                data["sid"] = sid
            self.send_json({"code": 0, "msg": "ok", "data": data})
        finally:
            conn.close()

    def post_login(self):
        cred = self.read_credentials()
        if cred is None:
            return
        user, pw = cred[0], cred[1]  # login 不需要邀请码
        conn = db()
        try:
            row = conn.execute("SELECT * FROM account WHERE user=?", (user,)).fetchone()
            if row is None:
                self.err(11, "账号或密码错误")
                return
            if row["lock_until"] and time.time() < row["lock_until"]:
                left = int((row["lock_until"] - time.time()) / 60) + 1
                self.err(12, "尝试次数过多,请%s分钟后再试" % left)
                return
            if hash_pw(pw, row["salt"]) != row["pwhash"]:
                with _db_lock:
                    fails = (row["fails"] or 0) + 1
                    lock = time.time() + LOCK_SECONDS if fails >= LOGIN_FAIL_MAX else 0
                    conn.execute("UPDATE account SET fails=?,lock_until=? WHERE user=?",
                                 (fails, lock, user))
                    conn.commit()
                self.err(11, "账号或密码错误")
                return
            with _db_lock:
                conn.execute("UPDATE account SET fails=0,lock_until=0,last_seen=? WHERE user=?",
                             (now(), user))
                conn.execute("UPDATE code SET last_seen=? WHERE code=?", (now(), row["code"]))
                # 挤号: 新登录签发新 sid,同账号旧会话(含正在线的那台)即刻失效
                sid = None
                if str(cred[3]) == "2":
                    sid = secrets.token_hex(8)
                    conn.execute("INSERT OR REPLACE INTO sess(code,sid,ts) VALUES(?,?,?)",
                                 (row["code"], sid, now()))
                conn.commit()
            data = {"user": user, "code": row["code"]}
            if sid:
                data["sid"] = sid
            self.send_json({"code": 0, "msg": "ok", "data": data})
        finally:
            conn.close()

    def post_hello(self):
        body = self.read_body(4096)
        if body is None:
            return
        payload = {}
        if body:
            try:
                payload = json.loads(body.decode("utf-8"))
            except Exception:
                self.err(5, "bad json")
                return
        else:
            payload = dict(self.query())  # 空 body 时允许 query 参数(?code=&name=)
        nc = norm_code(payload.get("code") or "")
        if not rate_allow("code:" + (nc or "new"), *RATE_CODE):
            self.err(9, "rate limited", 429)
            return
        name = (payload.get("name") or "")[:NAME_MAX]
        code = self.check_code({"code": payload.get("code") or ""}, create=True, name=name)
        if code is None:
            return
        conn = db()
        try:
            slots = []
            rows = conn.execute(
                """SELECT s.* FROM slot s JOIN
                   (SELECT code,slot,MAX(ver) mv FROM slot WHERE code=? GROUP BY slot) m
                   ON s.code=m.code AND s.slot=m.slot AND s.ver=m.mv
                   ORDER BY s.slot""", (code,)).fetchall()
            for r in rows:
                slots.append({"slot": r["slot"], "ver": r["ver"], "ts": r["ts"],
                              "size": r["size"], "md5": r["md5"], "name": r["name"],
                              "chain": r["chain"], "vg": r["ver_game"]})
            prof = {}
            for r in conn.execute(
                    "SELECT * FROM profile WHERE code=?", (code,)).fetchall():
                prof[r["fname"]] = {"ts": r["ts"], "size": r["size"], "md5": r["md5"]}
            gifts = [r["tf"] for r in conn.execute(
                "SELECT tf FROM gift_tf WHERE code=? ORDER BY tf", (code,)).fetchall()]
            # 周月懒结算(登录即触发) + 近14天发放台账=战报弹窗数据(客户端自行去重展示)
            with _db_lock:
                pvp_settle(conn, now())
            awards = [{"period": r["period"], "kind": r["kind"], "amt": r["amt"],
                       "detail": r["detail"], "ts": r["ts"]} for r in conn.execute(
                "SELECT period,kind,amt,detail,ts FROM pvp_award "
                "WHERE code=? AND ts>? ORDER BY ts DESC LIMIT 50",
                (code, now() - 14 * 86400)).fetchall()]
            self.send_json({"code": 0, "msg": "ok", "data": {
                "code": code, "slots": slots, "profile": prof, "gifts": gifts,
                "awards": awards, "server_time": now()}})
        finally:
            conn.close()

    def post_slot(self, q):
        code = self.check_code(q, create=True)
        if code is None:
            return
        if not rate_allow("code:" + code, *RATE_CODE):
            self.err(9, "rate limited", 429)
            return
        try:
            slot = int(q.get("slot", ""))
        except ValueError:
            self.err(1, "bad slot")
            return
        if not (SLOT_MIN <= slot <= SLOT_MAX):
            self.err(1, "bad slot")
            return
        md5 = (q.get("md5") or "").lower()
        if not re.match(r"^[0-9a-f]{32}$", md5):
            self.err(1, "bad md5")
            return
        try:
            chain = int(q.get("chain") or 0)
            vg = int(q.get("vg") or 0)
        except ValueError:
            chain, vg = 0, 0
        try:  # 反篡改计数: tp=硬超上限次数, td=漂移次数(客户端加密侧记账上报)
            tp = max(0, min(int(q.get("tp") or 0), TAMPER_TP_MAX))
            td = max(0, min(int(q.get("td") or 0), TAMPER_TP_MAX))
        except ValueError:
            tp, td = 0, 0
        name = unquote(q.get("name") or "")[:NAME_MAX]
        body = self.read_body(MAX_SLOT_BODY)
        if body is None:
            return
        if not body:
            self.err(6, "empty body")
            return
        real_md5 = hashlib.md5(body).hexdigest()
        if real_md5 != md5:
            self.err(7, "md5 mismatch")
            return
        ts = now()
        conn = db()
        try:
            with _db_lock:
                dup = conn.execute(
                    "SELECT ver,ts FROM slot WHERE code=? AND slot=? AND md5=? "
                    "ORDER BY ver DESC LIMIT 1", (code, slot, md5)).fetchone()
                if dup:  # 同内容重复上传: 幂等返回
                    conn.execute("UPDATE code SET last_seen=? WHERE code=?", (ts, code))
                    conn.commit()
                    self.send_json({"code": 0, "msg": "ok",
                                    "data": {"ver": dup["ver"], "ts": dup["ts"], "dup": 1}})
                    return
                mv = conn.execute("SELECT COALESCE(MAX(ver),0) v FROM slot "
                                  "WHERE code=? AND slot=?", (code, slot)).fetchone()["v"]
                ver = mv + 1
                # 反篡改打标: 篡改计数比历史水位涨了才记(打标供人工审查,不自动处置)
                prev = conn.execute(
                    "SELECT COALESCE(MAX(tp),0) t, COALESCE(MAX(td),0) d "
                    "FROM slot WHERE code=?", (code,)).fetchone()
                if tp > prev["t"] or (td >= DRIFT_FLAG_MIN and td > prev["d"]):
                    dupflag = conn.execute(
                        "SELECT 1 FROM flags WHERE code=? AND detail=? LIMIT 1",
                        (code, "tp=%d td=%d" % (tp, td))).fetchone()
                    if not dupflag:
                        conn.execute(
                            "INSERT INTO flags(code,kind,detail,ts) VALUES(?,?,?,?)",
                            (code, "tamper", "tp=%d td=%d" % (tp, td), ts))
                write_blob(code, "%d_%d.sav" % (slot, ver), body)
                conn.execute(
                    "INSERT INTO slot(code,slot,ver,ts,size,md5,name,chain,ver_game,tp,td) "
                    "VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                    (code, slot, ver, ts, len(body), md5, name, chain, vg, tp, td))
                # 版本轮转: 只留最近 MAX_VERSIONS 版
                old = conn.execute(
                    "SELECT ver FROM slot WHERE code=? AND slot=? ORDER BY ver DESC "
                    "LIMIT -1 OFFSET ?", (code, slot, MAX_VERSIONS)).fetchall()
                for r in old:
                    conn.execute("DELETE FROM slot WHERE code=? AND slot=? AND ver=?",
                                 (code, slot, r["ver"]))
                conn.execute("UPDATE code SET last_seen=? WHERE code=?", (ts, code))
                conn.commit()
                for r in old:
                    try:
                        os.remove(blob_path(code, "%d_%d.sav" % (slot, r["ver"])))
                    except OSError:
                        pass
            self.send_json({"code": 0, "msg": "ok", "data": {"ver": ver, "ts": ts}})
        finally:
            conn.close()

    # ---------- 天关排行榜 ----------
    _CTRL_RE = re.compile(r"[\x00-\x1f\x7f]")

    @classmethod
    def clean_board_name(cls, raw):
        """榜单名:去控制字符,NAME_MAX 字节内截断(不劈开 UTF-8 尾字节)。"""
        s = cls._CTRL_RE.sub("", str(raw or "").strip())
        while s and len(s.encode("utf-8")) > NAME_MAX:
            s = s[:-1]
        return s

    def post_tower(self, q):
        code = self.check_code(q)
        if code is None:
            return
        if not rate_allow("code:" + code, *RATE_CODE):
            self.err(9, "rate limited", 429)
            return
        try:
            floor = int(q.get("floor", ""))
        except ValueError:
            self.err(1, "bad floor")
            return
        if floor < 1:   # 不封顶(用户拍板2026-09-02:层数无上限,脏数据靠tamper门槛与一次性里程碑挡)
            self.err(1, "bad floor")
            return
        name = self.clean_board_name(q.get("name") or "")
        ts = now()
        conn = db()
        try:
            with _db_lock:
                # 只涨不跌:floor 取历史最高;name 每次刷新(随周目主角名);
                # ts 只在破纪录时更新=达成时刻
                conn.execute(
                    """INSERT INTO tower(code,floor,name,ts) VALUES(?,?,?,?)
                       ON CONFLICT(code) DO UPDATE SET
                         name=excluded.name,
                         floor=MAX(tower.floor, excluded.floor),
                         ts=CASE WHEN excluded.floor > tower.floor
                                 THEN excluded.ts ELSE tower.ts END""",
                    (code, floor, name, ts))
                # 天关账号天赋里程碑(100/500/1000/1500/2000层→天赋9500-9504):
                # 首达即推赠礼(hello gifts 通道带回,客户端按ID段入账号天赋层,
                # 不占SPTF格子);gift_tf 主键幂等,重报零副作用。
                for k, fl in enumerate(TOWER_TF_FLOORS):
                    if floor >= fl:
                        conn.execute(
                            "INSERT OR IGNORE INTO gift_tf(code,tf,ts,note) VALUES(?,?,?,?)",
                            (code, TOWER_TF_BASE + k, ts,
                             "天关%d层里程碑" % fl))
                conn.execute("UPDATE code SET last_seen=? WHERE code=?", (ts, code))
                conn.commit()
            row = conn.execute(
                "SELECT floor,ts FROM tower WHERE code=?", (code,)).fetchone()
            self.send_json({"code": 0, "msg": "ok",
                            "data": {"floor": row["floor"], "ts": row["ts"]}})
        finally:
            conn.close()

    def get_tower(self, q):
        code = self.check_code(q)
        if code is None:
            return
        try:
            top = int(q.get("top") or 50)
        except ValueError:
            top = 50
        top = max(1, min(top, TOWER_TOP_MAX))
        conn = db()
        try:
            rows = conn.execute(
                "SELECT code,floor,name,ts FROM tower "
                "ORDER BY floor DESC, ts ASC LIMIT ?", (top,)).fetchall()
            total = conn.execute("SELECT COUNT(*) c FROM tower").fetchone()["c"]
            me = conn.execute(
                "SELECT floor,name,ts FROM tower WHERE code=?", (code,)).fetchone()
            me_out = None
            if me:
                # 名次=严格排在我前面的条数+1,排序键与榜单一致(floor DESC, ts ASC)
                rank = conn.execute(
                    "SELECT COUNT(*) c FROM tower "
                    "WHERE floor>? OR (floor=? AND ts<?)",
                    (me["floor"], me["floor"], me["ts"])).fetchone()["c"] + 1
                me_out = {"rank": rank, "name": me["name"],
                          "floor": me["floor"], "ts": me["ts"]}
            out = [{"rank": i + 1, "name": r["name"], "floor": r["floor"],
                    "ts": r["ts"], "me": 1 if r["code"] == code else 0}
                   for i, r in enumerate(rows)]
            self.send_json({"code": 0, "msg": "ok",
                            "data": {"rows": out, "total": total, "me": me_out}})
        finally:
            conn.close()

    # ---------- 玩家对战(镜像挑战) ----------

    def post_pvp_snap(self, q):
        """上传镜像快照(一账号一份,覆盖式)。query: name/n(1..6)/pw/pw2/md5, body=blob。"""
        code = self.check_code(q, create=True)
        if code is None:
            return
        if not rate_allow("code:" + code, *RATE_CODE):
            self.err(9, "rate limited", 429)
            return
        try:
            n = int(q.get("n") or 0)
        except ValueError:
            n = 0
        if not (1 <= n <= PVP_TEAM_MAX):
            self.err(1, "bad n")
            return
        try:
            pw = max(0, min(int(q.get("pw") or 0), PVP_PW_MAX))
            pw2 = max(0, min(int(q.get("pw2") or 0), PVP_PW_MAX))
        except ValueError:
            pw = pw2 = 0
        name = self.clean_board_name(q.get("name") or "")
        md5 = (q.get("md5") or "").lower()
        if not re.match(r"^[0-9a-f]{32}$", md5):
            self.err(1, "bad md5")
            return
        body = self.read_body(PVP_SNAP_MAX)
        if body is None:
            return
        if not body:
            self.err(6, "empty body")
            return
        if hashlib.md5(body).hexdigest() != md5:
            self.err(7, "md5 mismatch")
            return
        ts = now()
        conn = db()
        try:
            with _db_lock:
                # pid 首次生成后保持稳定(榜单/挑战的对外句柄,不暴露云码);
                # bot 标同样随行保留(INSERT OR REPLACE 整行重建,不带着旧值会抹回 0)
                row = conn.execute("SELECT pid,bot FROM pvp_snap WHERE code=?", (code,)).fetchone()
                pid = row["pid"] if row else secrets.token_hex(6)
                bot = row["bot"] if row else 0
                write_blob(code, "pvp_team", body)
                conn.execute(
                    "INSERT OR REPLACE INTO pvp_snap(code,pid,name,n,pw,pw2,size,md5,ver,ts,bot) "
                    "VALUES(?,?,?,?,?,?,?,?,1,?,?)",
                    (code, pid, name, n, pw, pw2, len(body), md5, ts, bot))
                conn.execute(
                    "INSERT OR IGNORE INTO pvp_rating(code,score,wins,losses,games,ts) "
                    "VALUES(?,1000,0,0,0,?)", (code, ts))
                conn.execute("UPDATE code SET last_seen=? WHERE code=?", (ts, code))
                conn.commit()
        finally:
            conn.close()
        self.send_json({"code": 0, "msg": "ok",
                        "data": {"ts": ts, "size": len(body), "md5": md5}})

    def get_pvp_board(self, q):
        """论剑台榜。全员可挑战：有镜像+未ban+无tamper即入列(games<5 行 rank=null,
        前端显示"新");名次仅 games>=PVP_BOARD_MIN_GAMES 者有(否则冷启动死锁:
        上榜需打满5局,打局需挑战榜上人,无人上榜则无人可挑战)。"""
        code = self.check_code(q)
        if code is None:
            return
        try:
            top = int(q.get("top") or 50)
        except ValueError:
            top = 50
        top = max(1, min(top, PVP_TOP_MAX))
        base = ("FROM pvp_rating r "
                "JOIN pvp_snap s ON s.code=r.code "
                "JOIN code c ON c.code=r.code AND c.banned=0 "
                "LEFT JOIN flags f ON f.code=r.code AND f.kind='tamper' "
                "LEFT JOIN pvp_player p ON p.code=r.code "
                "WHERE f.id IS NULL")
        conn = db()
        try:
            rows = conn.execute(
                "SELECT r.code,r.score,r.wins,r.losses,r.games,r.ts,"
                "s.pid,s.name,s.pw,s.n,s.bot,p.pname,p.title "
                + base + " ORDER BY s.bot, r.score DESC, r.wins DESC, r.ts ASC LIMIT ?",
                (top,)).fetchall()
            total = conn.execute("SELECT COUNT(*) c " + base).fetchone()["c"]
            # 名次只数 games>=门槛 者(全局一致,不受 top 截断影响)
            rank_rows = conn.execute(
                "SELECT r.code " + base + " AND r.games>=%d"
                " ORDER BY r.score DESC, r.wins DESC, r.ts ASC"
                % PVP_BOARD_MIN_GAMES).fetchall()
            rank_of = {r["code"]: i + 1 for i, r in enumerate(rank_rows)}
            me_row = conn.execute(
                "SELECT * FROM pvp_rating WHERE code=?", (code,)).fetchone()
            me = None
            if me_row is not None:
                flagged = conn.execute(
                    "SELECT 1 FROM flags WHERE code=? AND kind='tamper' LIMIT 1",
                    (code,)).fetchone()
                has_snap = conn.execute(
                    "SELECT 1 FROM pvp_snap WHERE code=?", (code,)).fetchone()
                listed = bool(me_row["games"] >= PVP_BOARD_MIN_GAMES
                              and not flagged and has_snap)
                me = {"rank": rank_of.get(code), "score": me_row["score"],
                      "wins": me_row["wins"], "losses": me_row["losses"],
                      "games": me_row["games"], "listed": 1 if listed else 0}
            out = [{"rank": rank_of.get(r["code"]),
                    "isme": 1 if r["code"] == code else 0,
                    "bot": 1 if r["bot"] else 0,
                    "pid": r["pid"],
                    "name": r["pname"] or r["name"],   # 玩家名优先,无则镜像主角名
                    "sname": r["name"], "title": r["title"] or "",
                    "score": r["score"], "wins": r["wins"], "losses": r["losses"],
                    "games": r["games"], "pw": r["pw"], "n": r["n"], "ts": r["ts"]}
                   for r in rows]
            self.send_json({"code": 0, "msg": "ok",
                            "data": {"rows": out, "total": total, "me": me}})
        finally:
            conn.close()

    def get_pvp_match(self, q):
        """匹配挑战:服务端随机出三档对手,三选一。
        槽1=真人分接近(胜+3币)/槽2=真人分略低(胜+2币)/槽3=名宿bot(胜+1币)。
        真人不足时逐档放宽(±150→±500→任意真人),槽3无bot则留空(客户端容错)。"""
        code = self.check_code(q)
        if code is None:
            return
        conn = db()
        try:
            me = conn.execute("SELECT score FROM pvp_rating WHERE code=?",
                              (code,)).fetchone()
            my = me["score"] if me else 1000
            base = ("FROM pvp_rating r "
                    "JOIN pvp_snap s ON s.code=r.code "
                    "JOIN code c ON c.code=r.code AND c.banned=0 "
                    "LEFT JOIN flags f ON f.code=r.code AND f.kind='tamper' "
                    "LEFT JOIN pvp_player p ON p.code=r.code "
                    "WHERE f.id IS NULL AND r.code!=? ")
            used = []

            def q_slot(bot_val, cond, args):
                sql = ("SELECT r.code,r.score,r.wins,r.losses,r.games,"
                       "s.pid,s.name,s.pw,s.n,s.bot,p.pname,p.title " + base
                       + " AND s.bot=%d " % bot_val + cond)
                params = [code] + args + used
                if used:
                    sql += " AND r.code NOT IN (%s)" % ",".join("?" * len(used))
                return conn.execute(sql + " ORDER BY RANDOM() LIMIT 1",
                                    params).fetchone()

            # 槽1 分接近(±150→±500→任意真人)
            r1 = q_slot(0, " AND r.score BETWEEN ? AND ? ", [my - 150, my + 150])
            if r1 is None:
                r1 = q_slot(0, " AND r.score BETWEEN ? AND ? ", [my - 500, my + 500])
            if r1 is None:
                r1 = q_slot(0, "", [])
            if r1 is not None:
                used.append(r1["code"])
            # 槽2 分略低(低50~450→低于我→任意真人)
            r2 = q_slot(0, " AND r.score BETWEEN ? AND ? ", [my - 450, my - 50])
            if r2 is None:
                r2 = q_slot(0, " AND r.score < ? ", [my])
            if r2 is None:
                r2 = q_slot(0, "", [])
            if r2 is not None:
                used.append(r2["code"])
            # 槽3 名宿陪练
            r3 = q_slot(1, "", [])
            rows = []
            for r, reward in ((r1, 3), (r2, 2), (r3, 1)):
                if r is None:
                    continue
                rows.append({
                    "pid": r["pid"], "reward": reward,
                    "name": r["pname"] or r["name"], "sname": r["name"],
                    "title": r["title"] or "", "bot": 1 if r["bot"] else 0,
                    "score": r["score"], "wins": r["wins"], "losses": r["losses"],
                    "games": r["games"], "pw": r["pw"], "n": r["n"]})
            self.send_json({"code": 0, "msg": "ok",
                            "data": {"rows": rows, "my_score": my}})
        finally:
            conn.close()

    def get_pvp_challenge(self, q):
        """发挑战令牌(当日 PVP_TOK_DAILY 次;对手须有镜像/未ban/无tamper标)。"""
        code = self.check_code(q)
        if code is None:
            return
        foe_pid = (q.get("foe") or "").strip()
        ts = now()
        conn = db()
        try:
            with _db_lock:
                frow = conn.execute(
                    "SELECT s.code,s.name,s.pw,s.n FROM pvp_snap s "
                    "JOIN code c ON c.code=s.code AND c.banned=0 WHERE s.pid=?",
                    (foe_pid,)).fetchone()
                if frow is None:
                    self.err(2, "对手不存在或未上传镜像")
                    return
                foe = frow["code"]
                if foe == code:
                    self.err(1, "不能挑战自己")
                    return
                if conn.execute("SELECT 1 FROM flags WHERE code=? AND kind='tamper' "
                                "LIMIT 1", (foe,)).fetchone():
                    self.err(3, "该侠客已淡出江湖")
                    return
                day = day_cn(ts)
                issued = conn.execute(
                    "SELECT COUNT(*) c FROM pvp_tok WHERE atk=? AND day=?",
                    (code, day)).fetchone()["c"]
                if issued >= PVP_TOK_DAILY:
                    self.err(9, "今日挑战次数已用完,明天再来")
                    return
                # 匹配挑战槽位奖励(1/2/3币,report 按此发;0=非匹配挑战走老逻辑)
                try:
                    reward = int(q.get("reward") or 0)
                except ValueError:
                    reward = 0
                if reward not in (0, 1, 2, 3):
                    reward = 0
                tok = secrets.token_hex(8)
                conn.execute(
                    "INSERT INTO pvp_tok(tok,atk,def,day,used,ts,reward) "
                    "VALUES(?,?,?,?,0,?,?)",
                    (tok, code, foe, day, ts, reward))
                conn.commit()
        finally:
            conn.close()
        self.send_json({"code": 0, "msg": "ok", "data": {
            "tok": tok, "ttl": PVP_TOK_TTL, "name": frow["name"],
            "pw": frow["pw"], "n": frow["n"]}})

    def get_pvp_snap(self, q):
        """凭令牌下载对手镜像 blob(带 X-Md5)。令牌在 report 时核销,下载不消费。"""
        code = self.check_code(q)
        if code is None:
            return
        tok = (q.get("tok") or "").strip()
        conn = db()
        try:
            trow = conn.execute(
                "SELECT * FROM pvp_tok WHERE tok=? AND atk=? AND used=0 AND ts>?",
                (tok, code, now() - PVP_TOK_TTL)).fetchone()
            if trow is None:
                self.err(2, "挑战令牌无效或已过期")
                return
            snap = conn.execute(
                "SELECT * FROM pvp_snap WHERE code=?", (trow["def"],)).fetchone()
            if snap is None:
                self.err(2, "对手镜像不存在")
                return
        finally:
            conn.close()
        try:
            with open(blob_path(trow["def"], "pvp_team"), "rb") as f:
                data = f.read()
        except OSError:
            self.err(8, "blob missing", 500)
            return
        self.send_blob(data, snap["md5"])

    def post_pvp_report(self, q):
        """战报上报+ELO结算。query: foe(pid)/mode(1单挑2群战)/win(0/1)/tok。"""
        code = self.check_code(q)
        if code is None:
            return
        if not rate_allow("code:" + code, *RATE_CODE):
            self.err(9, "rate limited", 429)
            return
        try:
            mode = int(q.get("mode") or 0)
            win = int(q.get("win", ""))
        except ValueError:
            mode, win = 0, -1
        if mode not in (1, 2) or win not in (0, 1):
            self.err(1, "bad args")
            return
        tok = (q.get("tok") or "").strip()
        foe_pid = (q.get("foe") or "").strip()
        ts = now()
        day = day_cn(ts)
        conn = db()
        try:
            with _db_lock:
                # 周期懒结算先行(本局流水计入新周期,上期按周期末快照结算)
                pvp_settle(conn, ts)
                trow = conn.execute(
                    "SELECT * FROM pvp_tok WHERE tok=? AND atk=? AND used=0 AND ts>?",
                    (tok, code, ts - PVP_TOK_TTL)).fetchone()
                if trow is None:
                    self.err(2, "挑战令牌无效或已过期")
                    return
                frow = conn.execute(
                    "SELECT code,bot FROM pvp_snap WHERE pid=?",
                    (foe_pid,)).fetchone()
                if frow is None or frow["code"] != trow["def"]:
                    self.err(1, "bad foe")
                    return
                foe = trow["def"]
                # 原子核销: 同一令牌并发上报只成一单(照邀请码核销写法)
                cur = conn.execute(
                    "UPDATE pvp_tok SET used=1 WHERE tok=? AND used=0", (tok,))
                if cur.rowcount != 1:
                    conn.rollback()
                    self.err(2, "该局已上报过")
                    return
                # 计分闸门: 当日计分场数 / 同对手场次(超限照常入库不计分)
                cnt = conn.execute(
                    "SELECT COUNT(*) c FROM pvp_match "
                    "WHERE atk=? AND day=? AND counted=1", (code, day)).fetchone()["c"]
                same = conn.execute(
                    "SELECT COUNT(*) c FROM pvp_match "
                    "WHERE atk=? AND def=? AND day=? AND counted=1",
                    (code, foe, day)).fetchone()["c"]
                counted = 1 if (cnt < PVP_COUNT_DAILY
                                and same < PVP_SAME_FOE_DAILY) else 0
                for c in (code, foe):
                    conn.execute(
                        "INSERT OR IGNORE INTO pvp_rating(code,score,wins,losses,games,ts) "
                        "VALUES(?,1000,0,0,0,?)", (c, ts))
                ra_row = conn.execute(
                    "SELECT * FROM pvp_rating WHERE code=?", (code,)).fetchone()
                rb_row = conn.execute(
                    "SELECT * FROM pvp_rating WHERE code=?", (foe,)).fetchone()
                ra, rb = ra_row["score"], rb_row["score"]
                da = db_delta = 0
                if counted:
                    na, nb, da = elo_update(ra, rb, elo_k(ra_row["games"]),
                                            elo_k(rb_row["games"]), win)
                    conn.execute(
                        "UPDATE pvp_rating SET score=?,wins=wins+?,losses=losses+?,"
                        "games=games+1,ts=? WHERE code=?",
                        (na, 1 if win else 0, 0 if win else 1, ts, code))
                    # 名宿(陪练)侧冻结:分数/胜负/games 全不动→games 恒<5 永不占榜位,
                    # ELO 定价恒按当前分。仅真人对手才双边结算。
                    if frow["bot"]:
                        nb, db_delta = rb, 0
                    else:
                        conn.execute(
                            "UPDATE pvp_rating SET score=?,wins=wins+?,losses=losses+?,"
                            "games=games+1,ts=? WHERE code=?",
                            (nb, 0 if win else 1, 1 if win else 0, ts, foe))
                        db_delta = nb - rb
                    ra, rb = na, nb
                # 论剑币: 计分胜+30(名宿减半)/计分负+5;匹配挑战令牌带 reward(1/2/3)→
                # 胜利改按槽位发。日阶梯(真人计分胜1/3/5场→50/30/50币)走台账幂等即时发放,
                # 旧"当日首胜+20"并入阶梯首档(2026-09改版)。
                coin_delta = 0
                if counted:
                    if win and trow["reward"]:
                        coin_delta = trow["reward"]
                    else:
                        coin_delta = (PVP_COIN_WIN_BOT if frow["bot"] else PVP_COIN_WIN) \
                            if win else PVP_COIN_LOSS
                    if win and not frow["bot"]:
                        wins_today = 1 + conn.execute(
                            "SELECT COUNT(*) c FROM pvp_match "
                            "WHERE atk=? AND day=? AND counted=1 AND win=1 AND bot=0",
                            (code, day)).fetchone()["c"]
                        for w, coin in PVP_DAY_TIERS:
                            if wins_today >= w and award_once(
                                    conn, code, "d%d" % day, "w%d" % w, ts, coin,
                                    "日%d胜" % w):
                                coin_delta += coin
                    if coin_delta:
                        _add_coins(conn, code, coin_delta, ts)
                conn.execute(
                    "INSERT INTO pvp_match(ts,day,atk,def,mode,win,tok,ra,rb,da,db,counted,bot) "
                    "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)",
                    (ts, day, code, foe, mode, win, tok, ra_row["score"],
                     rb_row["score"], da, db_delta, counted, 1 if frow["bot"] else 0))
                coin_now = None
                if counted:
                    coin_now = conn.execute(
                        "SELECT coin FROM pvp_player WHERE code=?", (code,)).fetchone()["coin"]
                conn.commit()
        finally:
            conn.close()
        self.send_json({"code": 0, "msg": "ok", "data": {
            "counted": counted, "score": ra, "delta": da,
            "foe_score": rb, "coin": coin_now, "coin_delta": coin_delta}})

    # ---------- 论剑台玩家资料/商店/在线 ----------

    def _pvp_player_row(self, conn, code):
        """pvp_player 行(无则建空行)。"""
        conn.execute(
            "INSERT OR IGNORE INTO pvp_player(code,pname,title,coin,ts) "
            "VALUES(?,'','',0,?)", (code, now()))
        return conn.execute(
            "SELECT * FROM pvp_player WHERE code=?", (code,)).fetchone()

    def get_pvp_me(self, q):
        """我的论剑台资料:玩家名/称号/论剑币/战绩。"""
        code = self.check_code(q)
        if code is None:
            return
        conn = db()
        try:
            with _db_lock:
                pvp_settle(conn, now())   # 论剑台界面入口兜底触发周月懒结算
                prow = self._pvp_player_row(conn, code)
                rrow = conn.execute(
                    "SELECT score,wins,losses,games FROM pvp_rating WHERE code=?",
                    (code,)).fetchone()
                titles = [r["item"] for r in conn.execute(
                    "SELECT item FROM pvp_buy WHERE code=? AND item LIKE 'title_%'",
                    (code,)).fetchall()]
            r = rrow or {"score": 1000, "wins": 0, "losses": 0, "games": 0}
            self.send_json({"code": 0, "msg": "ok", "data": {
                "pname": prow["pname"] or "", "title": prow["title"] or "",
                "coin": prow["coin"], "titles": titles,
                "score": r["score"], "wins": r["wins"],
                "losses": r["losses"], "games": r["games"]}})
        finally:
            conn.close()

    def post_pvp_name(self, q):
        """设玩家名:首次免费,之后 PVP_NAME_COST 币(原子扣)。全服唯一(忽略大小写)。"""
        body = self.read_body(4096)
        if body is None:
            return
        payload = {}
        if body:
            try:
                payload = json.loads(body.decode("utf-8"))
            except Exception:
                self.err(5, "bad json")
                return
        if not payload.get("code"):
            payload["code"] = q.get("code")
        code = self.check_code(payload)
        if code is None:
            return
        name = str(payload.get("name") or "").strip()
        name = self.clean_board_name(name)
        if not (PVP_NAME_MIN <= len(name) <= PVP_NAME_MAX):
            self.err(10, "玩家名需%d~%d个字" % (PVP_NAME_MIN, PVP_NAME_MAX))
            return
        ts = now()
        conn = db()
        try:
            with _db_lock:
                prow = self._pvp_player_row(conn, code)
                dup = conn.execute(
                    "SELECT 1 FROM pvp_player WHERE pname=? COLLATE NOCASE "
                    "AND code<>?", (name, code)).fetchone()
                if dup:
                    self.err(11, "此名已有侠客在用")
                    return
                first = not prow["pname"]
                if not first and prow["coin"] < PVP_NAME_COST:
                    self.err(12, "论剑币不足(改名需%d)" % PVP_NAME_COST)
                    return
                conn.execute(
                    "UPDATE pvp_player SET pname=?,coin=coin-?,ts=? WHERE code=?",
                    (name, 0 if first else PVP_NAME_COST, ts, code))
                coin = conn.execute(
                    "SELECT coin FROM pvp_player WHERE code=?", (code,)).fetchone()["coin"]
                conn.commit()
        finally:
            conn.close()
        self.send_json({"code": 0, "msg": "ok", "data": {
            "pname": name, "coin": coin, "first": 1 if first else 0}})

    def get_pvp_shop(self, q):
        """商店目录+我的已购+余额。daily 商品附 dayleft=今日剩余可购件数。"""
        code = self.check_code(q)
        if code is None:
            return
        conn = db()
        try:
            with _db_lock:
                prow = self._pvp_player_row(conn, code)
                owned = {r["item"] for r in conn.execute(
                    "SELECT DISTINCT item FROM pvp_buy WHERE code=?",
                    (code,)).fetchall()}
                today = day_cn(now())
                daycnt = {}
                for r in conn.execute(
                        "SELECT item, ts FROM pvp_buy WHERE code=? AND ts>?",
                        (code, now() - 86400)).fetchall():
                    if day_cn(r["ts"]) == today:
                        daycnt[r["item"]] = daycnt.get(r["item"], 0) + 1
                title = prow["title"] or ""
            items = []
            for it in PVP_SHOP:
                o = dict(it)
                o["owned"] = 1 if it["id"] in owned else 0
                o["active"] = 1 if (it["kind"] == "title"
                                    and it["text"] == title) else 0
                if it.get("daily"):
                    o["dayleft"] = max(0, it["daily"] - daycnt.get(it["id"], 0))
                items.append(o)
            self.send_json({"code": 0, "msg": "ok", "data": {
                "coin": prow["coin"], "items": items}})
        finally:
            conn.close()

    def post_pvp_buy(self, q):
        """购买:原子验余额/扣币/记流水;once 类不可重复。返回发放指令由客户端执行。"""
        code = self.check_code(q)
        if code is None:
            return
        if not rate_allow("code:" + code, *RATE_CODE):
            self.err(9, "rate limited", 429)
            return
        item_id = (q.get("id") or "").strip()
        it = PVP_SHOP_IDX.get(item_id)
        if it is None:
            self.err(1, "bad id")
            return
        ts = now()
        conn = db()
        try:
            with _db_lock:
                prow = self._pvp_player_row(conn, code)
                if it["once"] and conn.execute(
                        "SELECT 1 FROM pvp_buy WHERE code=? AND item=? LIMIT 1",
                        (code, item_id)).fetchone():
                    self.err(2, "已拥有")
                    return
                # 每日限购:按当日(北京时区日界)pvp_buy流水计数
                if it.get("daily"):
                    today = day_cn(ts)
                    n = 0
                    for r in conn.execute(
                            "SELECT ts FROM pvp_buy WHERE code=? AND item=? AND ts>?",
                            (code, item_id, ts - 86400)).fetchall():
                        if day_cn(r["ts"]) == today:
                            n += 1
                    if n >= it["daily"]:
                        self.err(4, "今日限购%d件,明天再来" % it["daily"])
                        return
                if prow["coin"] < it["price"]:
                    self.err(3, "论剑币不足")
                    return
                conn.execute(
                    "UPDATE pvp_player SET coin=coin-?,ts=? WHERE code=?",
                    (it["price"], ts, code))
                conn.execute(
                    "INSERT INTO pvp_buy(code,item,ts) VALUES(?,?,?)",
                    (code, item_id, ts))
                # 买称号即佩带(后可免费切换)
                if it["kind"] == "title":
                    conn.execute(
                        "UPDATE pvp_player SET title=? WHERE code=?",
                        (it["text"], code))
                # 名剑:入账号仓库(2026-09-03改版:一律直发对应剑,升星只走仓库
                # "合成名剑"/"精魄升星";轩辕已满星则折算精魄);不再回发物品指令
                acc_iid = 0
                if it["kind"] == "thing" and it["thing"] in SWORD_IDS:
                    if it["thing"] == 631:
                        acc_iid, _gn = xy_grant_reward(conn, code, ts)
                    else:
                        acc_iid = it["thing"]
                        acc_add(conn, code, it["thing"], it["num"], ts)
                coin = conn.execute(
                    "SELECT coin FROM pvp_player WHERE code=?", (code,)).fetchone()["coin"]
                conn.commit()
        finally:
            conn.close()
        grant = {"kind": it["kind"]}
        if it["kind"] in ("thing", "gold"):
            grant["thing"] = it["thing"]
            grant["num"] = it["num"]
            if it["kind"] == "thing" and it["thing"] in SWORD_IDS:
                grant["kind"] = "acc"          # 客户端据此提示"已存入论剑台仓库"
                if acc_iid:
                    grant["thing"] = acc_iid   # 满星折算时=700(客户端toast点名精魄)
        elif it["kind"] == "title":
            grant["text"] = it["text"]
        self.send_json({"code": 0, "msg": "ok", "data": {
            "coin": coin, "grant": grant}})

    # ---------- 论剑台账号物品仓库(单机物品零入口;出图即离池) ----------

    @staticmethod
    def _dep_budget(conn, code, iid):
        """名剑/精魄回存额度=累计出图(exit)-已回存(dep)。
        单机身上的名剑只可能来自出图(take),读通关前旧档反复结算刷回存的
        复制路在此封顶:第二次 dep 超过出图记录即拒。"""
        row = conn.execute(
            """SELECT COALESCE(SUM(CASE WHEN kind='exit' THEN amt END),0) e,
                      COALESCE(SUM(CASE WHEN kind='dep' THEN amt END),0) d
               FROM acc_dep WHERE code=? AND iid=?""", (code, iid)).fetchone()
        return row["e"] - row["d"]

    @staticmethod
    def _sess_load(held):
        """会话 held JSON→dict(容错)。"""
        try:
            d = json.loads(held or "{}")
            return d if isinstance(d, dict) else {}
        except Exception:
            return {}

    def get_pvp_store(self, q):
        """仓库快照:账号物品池 + 进图会话(?begin=1 开新会话)。
        begin 时若有旧会话(上次未出图/断线):held 全部回滚入池,不丢物品。"""
        code = self.check_code(q)
        if code is None:
            return
        begin = (q.get("begin") or "") == "1"
        ts = now()
        conn = db()
        try:
            with _db_lock:
                pvp_settle(conn, ts)
                if begin:
                    srow = conn.execute(
                        "SELECT held FROM acc_sess WHERE code=?", (code,)).fetchone()
                    if srow is not None:
                        for k, v in self._sess_load(srow["held"]).items():
                            acc_add(conn, code, int(k), int(v), ts)
                        conn.execute("DELETE FROM acc_sess WHERE code=?", (code,))
                    conn.execute(
                        "INSERT OR REPLACE INTO acc_sess(code,held,ts) VALUES(?,?,?)",
                        (code, "{}", ts))
                    conn.commit()
                pool = [[r["iid"], r["n"]] for r in conn.execute(
                    "SELECT iid,n FROM acc_item WHERE code=? AND n>0 ORDER BY iid",
                    (code,)).fetchall()]
                srow = conn.execute(
                    "SELECT held FROM acc_sess WHERE code=?", (code,)).fetchone()
                held = sorted([int(k), v]
                              for k, v in self._sess_load(srow["held"]).items()) \
                    if srow else []
            self.send_json({"code": 0, "msg": "ok", "data": {
                "pool": pool, "held": held, "in_map": 1 if srow else 0}})
        finally:
            conn.close()

    def post_pvp_store(self, q):
        """仓库会话操作。query: op(begin/out/in/use/exit/dep/forge/feed)/iid/n(/i2)。
        服务端权威 held: 取出→池入held;存回→held入池(仅限本会话取出的,防白嫖);
        使用→held扣减(战斗用掉的消耗品);出图→held清空离池,客户端把剩余转单机档物品;
        存入(dep)→单机名剑直入池(免会话,白名单名剑/精魄,通关自动回仓队列专用,
        额度=累计出图,封读档复制路);合成(forge)→池中两把名剑熔成收集线一把(星相加);
        喂魄(feed)→名剑精魄×XY_FEED_COST喂收集线+1★。"""
        code = self.check_code(q)
        if code is None:
            return
        if not rate_allow("code:" + code, *RATE_CODE):
            self.err(9, "rate limited", 429)
            return
        op = (q.get("op") or "").strip()
        try:
            iid = int(q.get("iid") or 0)
            n = max(1, min(int(q.get("n") or 1), 99))
        except ValueError:
            iid, n = 0, 1
        ts = now()
        conn = db()
        try:
            with _db_lock:
                if op == "begin":
                    srow = conn.execute(
                        "SELECT held FROM acc_sess WHERE code=?", (code,)).fetchone()
                    if srow is not None:
                        for k, v in self._sess_load(srow["held"]).items():
                            acc_add(conn, code, int(k), int(v), ts)
                        conn.execute("DELETE FROM acc_sess WHERE code=?", (code,))
                    conn.execute(
                        "INSERT OR REPLACE INTO acc_sess(code,held,ts) VALUES(?,?,?)",
                        (code, "{}", ts))
                    conn.commit()
                    self.send_json({"code": 0, "msg": "ok", "data": {"held": []}})
                    return
                if op == "dep":
                    # 单机名剑存回仓库(通关自动回仓队列专用)。
                    # 不需要仓库会话(通关回仓在论剑台外触发)。信任口径与 achclaim
                    # 的 CJPend 一致:服务端无法验证单机背包,只能信客户端一次;
                    # 白名单只放十大名剑(631-640基础/661-690月赛星级/691-699收集线/
                    # 701-754同名梯子)与名剑精魄(700),该通道不会被滥用成任意物品铸币口。
                    if not (631 <= iid <= 640 or 661 <= iid <= 699
                            or LADDER_BASE <= iid <= LADDER_END
                            or iid == MAT_ID):
                        self.err(3, "只能存放名剑/名剑精魄")
                        return
                    # 防复制额度:单机身上的名剑只可能来自出图(take),累计回存
                    # 不得超过累计出图——读通关前旧档反复结算的复制路在此封顶
                    bud = self._dep_budget(conn, code, iid)
                    if n > bud:
                        self.err(3, "超出可回存数量(出图记录可回存%d件)" % max(bud, 0))
                        return
                    acc_add(conn, code, iid, n, ts)
                    conn.execute(
                        "INSERT INTO acc_dep(code,iid,kind,amt,ts) VALUES(?,?,'dep',?,?)",
                        (code, iid, n, ts))
                    conn.commit()
                    self.send_json({"code": 0, "msg": "ok", "data": {
                        "iid": iid, "n": n}})
                    return
                srow = conn.execute(
                    "SELECT held FROM acc_sess WHERE code=?", (code,)).fetchone()
                if srow is None:
                    self.err(2, "未在论剑台(无仓库会话)")
                    return
                held = self._sess_load(srow["held"])
                if op == "forge":
                    # 合成名剑(星级相加):池中两把各耗1,熔成轩辕收集线一把
                    try:
                        i2 = int(q.get("i2") or 0)
                    except ValueError:
                        i2 = 0
                    nid, star, ferr = forge_xy(conn, code, iid, i2, ts)
                    if ferr:
                        self.err(3, ferr)
                        return
                    conn.commit()
                    self.send_json({"code": 0, "msg": "ok", "data": {
                        "iid": nid, "star": star}})
                    return
                if op == "feed":
                    # 精魄升星(2026-09-03改版:可喂任意名剑):
                    # iid=0喂轩辕收集线;iid=名剑星级剑喂该剑(服务端权威校验)
                    nid, star, ferr = feed_xy(conn, code, iid, ts)
                    if ferr:
                        self.err(3, ferr)
                        return
                    conn.commit()
                    self.send_json({"code": 0, "msg": "ok", "data": {
                        "iid": nid, "star": star}})
                    return
                if op == "out":
                    prow = conn.execute(
                        "SELECT n FROM acc_item WHERE code=? AND iid=?",
                        (code, iid)).fetchone()
                    if prow is None or prow["n"] < n:
                        self.err(3, "仓库数量不足")
                        return
                    conn.execute(
                        "UPDATE acc_item SET n=n-?,ts=? WHERE code=? AND iid=?",
                        (n, ts, code, iid))
                    conn.execute(
                        "DELETE FROM acc_item WHERE code=? AND iid=? AND n<=0",
                        (code, iid))
                    held[str(iid)] = int(held.get(str(iid)) or 0) + n
                elif op == "in":
                    have = int(held.get(str(iid)) or 0)
                    if have < n:
                        self.err(3, "身上数量不足(只能存回本次取出的)")
                        return
                    if have - n <= 0:
                        held.pop(str(iid), None)
                    else:
                        held[str(iid)] = have - n
                    acc_add(conn, code, iid, n, ts)
                elif op == "use":
                    have = int(held.get(str(iid)) or 0)
                    if have < n:
                        self.err(3, "数量不足")
                        return
                    if have - n <= 0:
                        held.pop(str(iid), None)
                    else:
                        held[str(iid)] = have - n
                elif op == "exit":
                    # 出图:剩余 held 一次性带回(客户端转单机档物品),会话结束
                    take = sorted([int(k), v] for k, v in held.items())
                    # 名剑/精魄出图记账(回存额度基准:dep 累计不得超过 exit 累计)
                    for tid, cnt in take:
                        if sword_star_of(tid) > 0 or tid == MAT_ID:
                            conn.execute(
                                "INSERT INTO acc_dep(code,iid,kind,amt,ts)"
                                " VALUES(?,?,'exit',?,?)", (code, tid, cnt, ts))
                    conn.execute("DELETE FROM acc_sess WHERE code=?", (code,))
                    conn.commit()
                    self.send_json({"code": 0, "msg": "ok", "data": {"take": take}})
                    return
                else:
                    self.err(1, "bad op")
                    return
                conn.execute(
                    "UPDATE acc_sess SET held=?,ts=? WHERE code=?",
                    (json.dumps(held, sort_keys=True), ts, code))
                conn.commit()
            self.send_json({"code": 0, "msg": "ok", "data": {
                "iid": iid, "n": n,
                "held": sorted([int(k), v] for k, v in held.items())}})
        finally:
            conn.close()

    # ---------- 成就领取(服务端可验证系:论剑币/称号) ----------

    def _ach_eligible(self, conn, code, cond):
        """按 cond 类型自查资格。返回 (bool, 详情)。"""
        kind = cond[0]
        if kind == "tower":
            row = conn.execute("SELECT floor FROM tower WHERE code=?", (code,)).fetchone()
            return (row is not None and row["floor"] >= cond[1]), "闯天关%d层" % cond[1]
        if kind in ("wins", "score", "games"):
            row = conn.execute(
                "SELECT wins,score,games FROM pvp_rating WHERE code=?", (code,)).fetchone()
            col = {"wins": "wins", "score": "score", "games": "games"}[kind]
            v = row[col] if row else 0
            return v >= cond[1], "%s%d" % ({"wins": "论剑胜场", "score": "论剑积分",
                                            "games": "计分局数"}[kind], cond[1])
        if kind == "wtop":
            row = conn.execute(
                "SELECT 1 FROM pvp_award WHERE code=? AND kind='wtop' LIMIT 1",
                (code,)).fetchone()
            return row is not None, "周榜前十"
        if kind == "mtop3":
            row = conn.execute(
                "SELECT 1 FROM pvp_award WHERE code=? AND kind IN ('m1','m2','m3') "
                "LIMIT 1", (code,)).fetchone()
            return row is not None, "月榜前三"
        if kind == "swords":
            swords = set()
            for r in conn.execute(
                    "SELECT iid FROM acc_item WHERE code=? AND n>0", (code,)).fetchall():
                iid = r["iid"]
                if 631 <= iid <= 640:
                    swords.add(iid)
                elif SWORD_STAR_BASE <= iid < SWORD_STAR_BASE + 30:
                    swords.add(631 + (iid - SWORD_STAR_BASE) // 3)
                elif XY_STAR_BASE <= iid <= XY_STAR_BASE + XY_MAX_STAR - 2:
                    swords.add(631)
            return len(swords) >= cond[1], "仓库持有%d种名剑" % len(swords)
        return False, "未知条件"

    def _claim_one(self, conn, code, ach, ts):
        """尝试领取单条服务端验证成就。
        返回 ("got", 结果dict) / ("claimed", 已领过) / ("notyet", 未达标详情)。
        先查资格再记账,全程无回滚,扫荡循环里安全。"""
        ok, need = self._ach_eligible(conn, code, ach["cond"])
        if not ok:
            return "notyet", need
        if not award_once(conn, code, "ach", "cj%d" % ach["aid"], ts,
                          ach.get("coin") or 0, "成就·" + ach["name"]):
            return "claimed", need
        if ach.get("coin"):
            _add_coins(conn, code, ach["coin"], ts)
        if ach.get("title"):
            conn.execute(
                "INSERT OR IGNORE INTO pvp_player(code,pname,title,coin,ts) "
                "VALUES(?,'','',0,?)", (code, ts))
            conn.execute("UPDATE pvp_player SET title=? WHERE code=?",
                         (ach["title"], code))
        d = {"aid": ach["aid"], "name": ach["name"],
             "coin_gain": ach.get("coin") or 0, "title": ach.get("title") or "",
             "need": need}
        if ach.get("coin"):
            d["coin"] = conn.execute(
                "SELECT coin FROM pvp_player WHERE code=?", (code,)).fetchone()["coin"]
        return "got", d

    def post_pvp_achclaim(self, q):
        """成就奖励领取。
        aid=具体槽位: PVP_ACH 系服务端自查资格→发放(币/称号);
                      ACH_TRUST 系(周目物品档)信任客户端判定,台账一次性,物品入仓库。
        aid=0: 扫荡模式,一次返回全部可领的 PVP_ACH(客户端进论剑台/战后调用)。"""
        code = self.check_code(q)
        if code is None:
            return
        if not rate_allow("code:" + code, *RATE_CODE):
            self.err(9, "rate limited", 429)
            return
        try:
            aid = int(q.get("aid") or 0)
        except ValueError:
            aid = 0
        ts = now()
        conn = db()
        try:
            with _db_lock:
                pvp_settle(conn, ts)
                if aid == 0:
                    got = []
                    for ach in PVP_ACH:
                        st, d = self._claim_one(conn, code, ach, ts)
                        if st == "got":
                            got.append(d)
                    conn.commit()
                    data = {"got": got}
                elif aid in PVP_ACH_IDX:
                    st, d = self._claim_one(conn, code, PVP_ACH_IDX[aid], ts)
                    if st == "claimed":
                        self.err(2, "已领取过")
                        return
                    if st == "notyet":
                        self.err(3, "尚未达成(%s)" % d)
                        return
                    conn.commit()
                    data = d
                elif aid in ACH_TRUST:
                    iid, n = ACH_TRUST[aid]
                    if not award_once(conn, code, "ach", "cj%d" % aid, ts, 0,
                                      "周目成就·物品入仓库"):
                        self.err(2, "已领取过")
                        return
                    acc_add(conn, code, iid, n, ts)
                    conn.commit()
                    data = {"aid": aid, "item": {"iid": iid, "n": n}}
                else:
                    self.err(1, "bad aid")
                    return
        finally:
            conn.close()
        self.send_json({"code": 0, "msg": "ok", "data": data})

    def post_pvp_title(self, q):
        """切换已拥有称号(免费);传空清除。"""
        code = self.check_code(q)
        if code is None:
            return
        text = self.clean_board_name((q.get("text") or "").strip())
        conn = db()
        try:
            with _db_lock:
                if text:
                    hit = conn.execute(
                        "SELECT 1 FROM pvp_buy WHERE code=? AND item=? LIMIT 1",
                        (code, "title_" + text)).fetchone()
                    if not hit:
                        self.err(2, "尚未拥有该称号")
                        return
                conn.execute("UPDATE pvp_player SET title=?,ts=? WHERE code=?",
                             (text, now(), code))
                conn.commit()
        finally:
            conn.close()
        self.send_json({"code": 0, "msg": "ok", "data": {"title": text}})

    def post_pvp_presence(self, q):
        """论剑台在线心跳:进程内表,TTL 过期即离线。返回在场名单(不含自己)。
        v2 同屏: 心跳可带 x/y/dir/walk(白名单校验,不合法当无坐标);
        响应每人多带 {score,wins,losses},有镜像加 {pid,pw,n},有坐标加
        {x,y,dir,walk};data.v=2 标记新协议(旧服务端无此键,客户端据此降级)。
        带坐标条目 TTL 6s(离开约5秒消失),旧客户端无坐标条目仍 40s。"""
        if not rate_allow("pvip:" + self.client_ip(), *RATE_PVP):
            self.err(9, "rate limited", 429)
            return
        code = self.check_code(q)
        if code is None:
            return
        if not rate_allow("pv:" + code, *RATE_PVP_CODE):
            self.err(9, "rate limited", 429)
            return
        leave = q.get("leave") or ""
        ts = time.time()  # 浮点秒:客户端拿相邻两跳 ts 差当插值周期(整秒截断误差1/1.5)

        def _int_arg(k, lo, hi):
            try:
                v = int(q.get(k, ""))
            except (ValueError, TypeError):
                return None
            return v if lo <= v <= hi else None

        x, y = _int_arg("x", 1, 63), _int_arg("y", 1, 63)
        d = _int_arg("dir", 0, 3)
        walk = (q.get("walk") or "").strip()
        if walk.isdigit() and len(walk) <= 3 and int(walk) <= 999:
            walk = walk.zfill(3)
        elif walk not in ("000m", "000m1", "000g", "000f"):
            walk = None
        has_pos = x is not None and y is not None

        prow = srow = rrow = None
        if not leave:
            conn = db()
            try:
                with _db_lock:
                    prow = conn.execute(
                        "SELECT pname,title FROM pvp_player WHERE code=?",
                        (code,)).fetchone()
                    srow = conn.execute(
                        "SELECT pid,name,pw,n FROM pvp_snap WHERE code=?",
                        (code,)).fetchone()
                    rrow = conn.execute(
                        "SELECT score,wins,losses FROM pvp_rating WHERE code=?",
                        (code,)).fetchone()
            finally:
                conn.close()
        players = []
        with _pvp_online_lock:
            if leave:
                _PVP_ONLINE.pop(code, None)
            else:
                nm = (prow["pname"] if prow and prow["pname"] else
                      (srow["name"] if srow else "")) or "无名侠客"
                _PVP_ONLINE[code] = {
                    "nm": nm, "title": prow["title"] if prow else "", "ts": ts,
                    "x": x if has_pos else None, "y": y if has_pos else None,
                    "dir": d if has_pos else None,
                    "walk": walk if has_pos else None,
                    "pid": srow["pid"] if srow else None,
                    "pw": srow["pw"] if srow else 0,
                    "n": srow["n"] if srow else 0,
                    "score": rrow["score"] if rrow else 1000,
                    "wins": rrow["wins"] if rrow else 0,
                    "losses": rrow["losses"] if rrow else 0}
            for c, v in list(_PVP_ONLINE.items()):
                ttl = (PVP_ONLINE_TTL_POS if v.get("x") is not None
                       else PVP_ONLINE_TTL)
                if ts - v["ts"] > ttl:
                    del _PVP_ONLINE[c]
                    continue
                if c != code:
                    players.append(v)
        players.sort(key=lambda v: v["ts"])    # 进场序稳定,面板名单不闪
        out = []
        for v in players:
            p = {"name": v["nm"], "title": v["title"], "score": v["score"],
                 "wins": v["wins"], "losses": v["losses"], "ts": v["ts"]}
            if v.get("pid"):
                p.update(pid=v["pid"], pw=v["pw"], n=v["n"])
            if v.get("x") is not None:
                p.update(x=v["x"], y=v["y"], dir=v["dir"] or 0,
                         walk=v["walk"] or "000m")
            out.append(p)
        data = {"count": len(out) + (0 if leave else 1), "players": out, "v": 2}
        # 组队捎带:我的队伍 + 待处理邀请(1.5s 心跳即轮询通道,省一条长轮询)
        if not leave:
            with _pvp_online_lock:
                online_codes = set(_PVP_ONLINE.keys())
            conn = db()
            try:
                with _db_lock:
                    conn.execute("DELETE FROM party_invite WHERE ts < ?",
                                 (ts - PARTY_INVITE_TTL,))
                    party = _party_info(conn, code, online_codes)
                    invs = conn.execute(
                        """SELECT i.from_code, i.ts FROM party_invite i
                           WHERE i.to_code=? ORDER BY i.ts DESC LIMIT 3""",
                        (code,)).fetchall()
                    invites = []
                    for iv in invs:
                        prow = conn.execute(
                            "SELECT pname FROM pvp_player WHERE code=?",
                            (iv["from_code"],)).fetchone()
                        srow = conn.execute(
                            "SELECT name FROM pvp_snap WHERE code=?",
                            (iv["from_code"],)).fetchone()
                        nm = (prow["pname"] if prow and prow["pname"] else
                              (srow["name"] if srow else "")) or "无名侠客"
                        invites.append({"from": iv["from_code"], "name": nm,
                                        "ts": iv["ts"]})
                    conn.commit()
                data["party"] = party or {}   # 空表=明确无队(与旧服务端不带键区分)
                data["invites"] = invites
            finally:
                conn.close()
        self.send_json({"code": 0, "msg": "ok", "data": data})

    def post_pvp_party(self, q):
        """组队操作。op=invite(需 pid/name/code 之一指目标)/accept/decline/leave/disband/info
        队长制:invite/accept 建队入队;队长退出自动转让给最早队员;空队自清。"""
        code = self.check_code(q)
        if code is None:
            return
        op = (q.get("op") or "").strip()
        ts = now()
        conn = db()
        try:
            with _db_lock:
                msg = "ok"
                if op == "invite":
                    tgt = _resolve_target(conn, q)
                    if not tgt:
                        self.err(2, "找不到该玩家")
                        return
                    if tgt == code:
                        self.err(2, "不能邀请自己")
                        return
                    p = _party_of(conn, code)
                    if p is not None and p["leader"] != code:
                        self.err(2, "只有队长可以邀请")
                        return
                    if _party_of(conn, tgt) is not None:
                        self.err(2, "对方已在队伍中")
                        return
                    if p is None:
                        cur = conn.execute(
                            "INSERT INTO party(leader, ts) VALUES(?,?)",
                            (code, ts))
                        pid_ = cur.lastrowid
                        conn.execute(
                            "INSERT OR REPLACE INTO party_member(party_id, code, ts)"
                            " VALUES(?,?,?)", (pid_, code, ts))
                    else:
                        pid_ = p["id"]
                    n_mem = conn.execute(
                        "SELECT COUNT(*) c FROM party_member WHERE party_id=?",
                        (pid_,)).fetchone()["c"]
                    n_inv = conn.execute(
                        "SELECT COUNT(DISTINCT to_code) c FROM party_invite"
                        " WHERE party_id=?", (pid_,)).fetchone()["c"]
                    if n_mem + n_inv >= PARTY_MAX:
                        self.err(2, "队伍已满(含待处理邀请)")
                        return
                    conn.execute(
                        "INSERT OR REPLACE INTO party_invite(to_code, from_code,"
                        " party_id, ts) VALUES(?,?,?,?)", (tgt, code, pid_, ts))
                    msg = "已发出邀请"
                elif op == "accept":
                    frm = norm_code(q.get("from") or "")
                    iv = conn.execute(
                        "SELECT * FROM party_invite WHERE to_code=? AND from_code=?",
                        (code, frm)).fetchone()
                    if iv is None or ts - iv["ts"] > PARTY_INVITE_TTL:
                        self.err(2, "邀请已失效")
                        return
                    p = conn.execute(
                        "SELECT * FROM party WHERE id=?", (iv["party_id"],)).fetchone()
                    if p is None:
                        self.err(2, "队伍已解散")
                        return
                    n_mem = conn.execute(
                        "SELECT COUNT(*) c FROM party_member WHERE party_id=?",
                        (p["id"],)).fetchone()["c"]
                    if n_mem >= PARTY_MAX:
                        self.err(2, "队伍已满")
                        return
                    # 一人一队:先退旧队(连带队长转让/空队清理)
                    self._party_leave(conn, code, ts)
                    conn.execute(
                        "INSERT OR REPLACE INTO party_member(party_id, code, ts)"
                        " VALUES(?,?,?)", (p["id"], code, ts))
                    conn.execute("DELETE FROM party_invite WHERE to_code=?", (code,))
                    msg = "已入队"
                elif op == "decline":
                    frm = norm_code(q.get("from") or "")
                    conn.execute(
                        "DELETE FROM party_invite WHERE to_code=? AND from_code=?",
                        (code, frm))
                    msg = "已拒绝"
                elif op == "leave":
                    self._party_leave(conn, code, ts)
                    msg = "已离队"
                elif op == "disband":
                    p = _party_of(conn, code)
                    if p is None:
                        self.err(2, "你不在队伍中")
                        return
                    if p["leader"] != code:
                        self.err(2, "只有队长可以解散")
                        return
                    conn.execute("DELETE FROM party_member WHERE party_id=?",
                                 (p["id"],))
                    conn.execute("DELETE FROM party_invite WHERE party_id=?",
                                 (p["id"],))
                    conn.execute("DELETE FROM party WHERE id=?", (p["id"],))
                    msg = "已解散"
                elif op == "info":
                    pass
                else:
                    self.err(1, "bad op")
                    return
                with _pvp_online_lock:
                    online_codes = set(_PVP_ONLINE.keys())
                party = _party_info(conn, code, online_codes)
                conn.commit()
                self.send_json({"code": 0, "msg": msg, "data": {"party": party}})
        finally:
            conn.close()

    def _party_leave(self, conn, code, ts):
        """退队(内部):队长退出→转让最早队员;空队连邀请一起清"""
        p = _party_of(conn, code)
        if p is None:
            return
        conn.execute("DELETE FROM party_member WHERE party_id=? AND code=?",
                     (p["id"], code))
        conn.execute("DELETE FROM party_invite WHERE from_code=?", (code,))
        rest = conn.execute(
            "SELECT code FROM party_member WHERE party_id=? ORDER BY ts, rowid LIMIT 1",
            (p["id"],)).fetchone()
        if rest is None:
            conn.execute("DELETE FROM party_invite WHERE party_id=?", (p["id"],))
            conn.execute("DELETE FROM party WHERE id=?", (p["id"],))
        elif p["leader"] == code:
            conn.execute("UPDATE party SET leader=? WHERE id=?",
                         (rest["code"], p["id"]))

    def get_slot(self, q):
        code = self.check_code(q)
        if code is None:
            return
        try:
            slot = int(q.get("slot", ""))
        except ValueError:
            self.err(1, "bad slot")
            return
        if not (SLOT_MIN <= slot <= SLOT_MAX):
            self.err(1, "bad slot")
            return
        try:
            ver = int(q["ver"]) if q.get("ver") else None
        except ValueError:
            ver = None
        conn = db()
        try:
            if ver is None:
                row = conn.execute(
                    "SELECT * FROM slot WHERE code=? AND slot=? ORDER BY ver DESC LIMIT 1",
                    (code, slot)).fetchone()
            else:
                row = conn.execute(
                    "SELECT * FROM slot WHERE code=? AND slot=? AND ver=?",
                    (code, slot, ver)).fetchone()
            if row is None:
                self.err(2, "not found")
                return
        finally:
            conn.close()
        try:
            with open(blob_path(code, "%d_%d.sav" % (slot, row["ver"])), "rb") as f:
                data = f.read()
        except OSError:
            self.err(8, "blob missing", 500)
            return
        self.send_blob(data, row["md5"])

    def post_profile(self, q):
        code = self.check_code(q, create=True)
        if code is None:
            return
        if not rate_allow("code:" + code, *RATE_CODE):
            self.err(9, "rate limited", 429)
            return
        fname = q.get("name") or ""
        if fname not in PROFILE_NAMES:
            self.err(1, "bad name")
            return
        md5 = (q.get("md5") or "").lower()
        body = self.read_body(MAX_PROFILE_BODY)
        if body is None:
            return
        if not body:
            self.err(6, "empty body")
            return
        real = hashlib.md5(body).hexdigest()
        if md5 and real != md5:
            self.err(7, "md5 mismatch")
            return
        ts = now()
        conn = db()
        try:
            with _db_lock:
                write_blob(code, fname, body)
                conn.execute(
                    "INSERT OR REPLACE INTO profile(code,fname,ts,size,md5) "
                    "VALUES(?,?,?,?,?)", (code, fname, ts, len(body), real))
                conn.execute("UPDATE code SET last_seen=? WHERE code=?", (ts, code))
                conn.commit()
        finally:
            conn.close()
        self.send_json({"code": 0, "msg": "ok", "data": {"ts": ts, "md5": real}})

    def get_profile(self, q):
        code = self.check_code(q)
        if code is None:
            return
        fname = q.get("name") or ""
        if fname not in PROFILE_NAMES:
            self.err(1, "bad name")
            return
        conn = db()
        try:
            row = conn.execute("SELECT * FROM profile WHERE code=? AND fname=?",
                               (code, fname)).fetchone()
        finally:
            conn.close()
        if row is None:
            self.err(2, "not found")
            return
        try:
            with open(blob_path(code, fname), "rb") as f:
                data = f.read()
        except OSError:
            self.err(8, "blob missing", 500)
            return
        self.send_blob(data, row["md5"])


def main():
    init_db()
    srv = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    srv.daemon_threads = True
    print("cloudsave api listening on 127.0.0.1:%d" % PORT, flush=True)
    srv.serve_forever()


if __name__ == "__main__":
    main()
