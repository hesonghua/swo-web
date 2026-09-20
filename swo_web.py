#!/usr/bin/env python3
"""swo_web.py -- SWO/调试 Web 控制台（PC host 版，jtag_swd_dbg + 板上 jtag_tool 后端）

单文件、零依赖（python3 标准库），跑在 PC 上，经网络连板上 jtag_tool 服务：
  * 板上先停 openocd，然后 `jtag_tool --serve`（tmux 后台；默认口可改）：
      - 命令口 <board>:5555（行文本，每命令应答后缀 Z<seq>D 标记）
        halt/resume/step/reg/mdw/bp/wp/swo_tpiu…… 全套 jtag_tool shell
      - SWO 流口 <board>:5556（原始字节直推，服务端 2ms 从 IP FIFO 排水）
  * SWO 流本进程内解析 ITM/DWT 包：
      - stimulus port0 文本  -> SSE 实时控制台；port1-31 多通道终端
      - 事件端口（默认 2）   -> 1B type + 4B arg 定长记录 -> 统一时间线
      - PC 采样包 (0x17)     -> 热点直方图（ELF 符号化，可跳反汇编）
      - 异常跟踪包 (0x0E)    -> entry/exit/ret 配时统计
      - 时间戳包             -> GTC 时间线（72MHz = HCLK，实测钉死）
  * 调试器视图：核心寄存器（halt 快照 + xPSR 解码）、内存浏览器（读写/
    符号跳转）、FPB 断点/DWT 观察点管理（免 halt 随时下）、单步
  * 反汇编：host 侧 arm-none-eabi-objdump 缓存（-d/-S 源码交错），当前
    PC 高亮、热点/跳转定位
  * 变量 watch：ELF STT_OBJECT 全局符号 mdw 采样 -> 时间曲线
  * HTTP :8080 出一个单页 UI（无外部资源）

连接建立自动代配 swo_tpiu（traceclk 默认 72M，目标页可改/重配）。

用法:  python3 swo_web.py [board_host] [port] [elf_path]
       board_host 默认 elink.local；elf_path 缺省用 swotest.elf——板 IP 常漂移（双网卡 .143/.168），
       每次重连都重新 mDNS 解析，无需重启
注意:  jtag_tool 每个端口单客户端；换固件仍需短暂起 openocd（jtag_tool
       无 flash 编程器），用完记得停掉再起 --serve。
"""

import asyncio
import base64
import bisect
import faulthandler
import hashlib
import json
import os
import re
import shutil
import signal
import socket
import struct
import subprocess
import sys
import time
from collections import deque

faulthandler.register(signal.SIGUSR1, all_threads=True)  # kill -USR1 转储栈

BOARD_HOST = "elink.local"
OCD_PORT = 5555            # 板上 jtag_tool --serve 命令口
SWO_PORT = 5556            # jtag_tool --serve SWO 流口
SWO_PINFREQ_DEFAULT = 8000000  # 默认 8M：PC 57K/s + 异常满速最佳平衡
                            # （72M/72 与 AXI 125M/125），4M 档有 +0.8% 失配
                            # → 每字节 8% 位漂 → 静默位滑动（FE 测不出）
_ELF_CANDIDATES = [
    os.path.join(os.path.dirname(os.path.abspath(__file__)),
                 "..", "swotest", "swotest.elf"),
    "/root/swotest.elf",
]
DEFAULT_ELF = next((p for p in _ELF_CANDIDATES if os.path.exists(p)),
                   _ELF_CANDIDATES[0])


def board_addr(host=None):
    """解析板地址：数字 IP 直用（avahi 对 IP 会白等 3s 且同步阻塞整个
     * 事件循环——曾致 swo_loop 停读 5556 → 板侧 write 阻塞 serve 循环
     * → 命令饿死的连锁），主机名才走 mDNS。"""
    host = host or BOARD_HOST
    try:
        socket.inet_pton(socket.AF_INET, host)
        return host
    except OSError:
        pass
    try:
        out = subprocess.run(["avahi-resolve", "-4", "-n", host],
                             capture_output=True, text=True, timeout=3)
        parts = out.stdout.split()
        if len(parts) >= 2:
            return parts[1]
    except Exception:
        pass
    try:
        return socket.gethostbyname(host)
    except OSError:
        return host
GTC_HZ = 72_000_000  # M3 r1p1 实测：GTC = HCLK
SIZE = {1: 1, 2: 2, 3: 4}  # ITM 包头 bits[1:0] 长度码（3 = 4 字节!）
DWT_CTRL = 0xE0001000
PCSAMPLENA, EXCTRCENA, CYCCNTENA = 1 << 12, 1 << 16, 1 << 0


# ---------------------------------------------------------------- ELF 符号表
def load_symbols(path):
    """纯 struct 解析 ELF .symtab，返回 (funcs, objs, by_name)：
    funcs = 按地址排序的 [(addr, size, name)]（STT_FUNC，剖析/反汇编用），
    objs  = 同结构（STT_OBJECT，内存跳转/变量 watch 用），
    by_name = {name: (addr, size)}（函数+变量，符号名查地址用）。
    过滤 $d/$t 映射符号。"""
    try:
        data = open(path, "rb").read()
    except OSError:
        return [], [], {}
    if data[:4] != b"\x7fELF":
        return [], [], {}
    is64 = data[4] == 2
    if is64:
        shoff = struct.unpack_from("<Q", data, 0x28)[0]
        shentsize, shnum = struct.unpack_from("<HH", data, 0x3A)
        shfmt = "<IIQQQQIIQQ"
    else:
        shoff = struct.unpack_from("<I", data, 0x20)[0]
        shentsize, shnum = struct.unpack_from("<HH", data, 0x2E)
        shfmt = "<IIIIIIIIII"
    shs = []
    for i in range(shnum):
        sh = struct.unpack_from(shfmt, data, shoff + i * shentsize)
        shs.append(sh)  # name,type,flags,addr,offset,size,link,info,...
    symtab = strtab = None
    for sh in shs:
        if sh[1] == 2:  # SHT_SYMTAB
            symtab = sh
            strtab = shs[sh[6]]
            break
    funcs, objs, by_name = [], [], {}
    if not symtab:
        return funcs, objs, by_name
    buf = data[strtab[4]:strtab[4] + strtab[5]]

    def sname(off):
        end = buf.find(b"\0", off)
        return buf[off:end].decode(errors="replace")

    off, entsz = symtab[4], symtab[9] or (24 if is64 else 16)
    for i in range(symtab[5] // entsz):
        if is64:
            no, _, info, _, val, sz = struct.unpack_from("<IBBHQQ", data, off + i * entsz)
        else:
            no, val, sz, info, _, _ = struct.unpack_from("<IIIBBH", data, off + i * entsz)
        styp = info & 0xF
        if styp not in (1, 2) or sz == 0 or val == 0:  # STT_OBJECT / STT_FUNC
            continue
        name = sname(no)
        if not name or name.startswith("$"):
            continue
        if styp == 2:
            val &= 0xFFFFFFFE        # 函数符号带 Thumb bit0，bp/跳转前剥掉
        (funcs if styp == 2 else objs).append((val, sz, name))
        # 同名多符号（局部 static 同名）：只留第一个（按地址序后面覆盖不了）
        if name not in by_name:
            by_name[name] = (val, sz)
    funcs.sort()
    objs.sort()
    return funcs, objs, by_name


# ---------------------------------------------------------------- 全局状态
class State:
    def __init__(self):
        self.t0 = time.time()
        # 控制台
        self.text = deque(maxlen=40000)
        self.con_queues = set()
        # PC 采样
        self.pc_hist = {}
        self.pc_total = 0
        self.pc_t0 = time.time()
        self.pc_sleep = 0
        # 异常跟踪
        self.exc = {}  # exc -> stats dict
        self.exc_events = 0
        self.exc_recent = deque(maxlen=40)
        # 等待 ts 定时的队列：异常项 ("exc",kind,num) 与 ITM 事件项
        # ("evt",type,arg) 并发时靠 deque 保最近若干个；ts 只给最后一个精确定时
        self._awaiting = deque(maxlen=8)
        self.last_ret = None
        self.last_exit = None
        self.r_sum = 0
        self.r_n = 0
        self.exc_mispaired = 0
        self.exc_diag = {}  # (kind,exc)->count 诊断
        # 流健康度
        self.resyncs = 0
        self.overflows = 0
        self.gtc = 0
        # DWT 轮询
        self.mhz = 0.0
        self.exc_ps = 0.0
        self.sleep_pct = 0.0
        self.dwt_raw = [0] * 6
        self.pc_on = False
        self.exc_on = False
        # 连接
        self.ocd_ok = False
        self.swo_ok = False
        self.swo_traceclk = 72000000  # swo_tpiu 代配的 traceclk（目标 HCLK）
        self.swo_baud = SWO_PINFREQ_DEFAULT  # SWO 引脚波特率（8M 默认）
        self.swo_state = "init"
        self.swo_conn_n = 0
        self.swo_last_rx = 0.0
        self.swo_last_err = ""
        self.elf_path = DEFAULT_ELF
        self.syms = []          # STT_FUNC [(addr,size,name)]
        self.objs = []          # STT_OBJECT [(addr,size,name)]
        self.sym_by_name = {}   # name -> (addr,size)
        # 目标状态（tgt_loop 维护）
        self.tgt_state = "unknown"   # running | halted | unknown
        self.halt_reason = ""
        self.halt_pc = None
        self.regs = {}          # halt 快照 name -> int
        self.bps = []           # [{"addr":int,"len":int,"hw":bool}]
        self.wps = []           # [{"addr":int,"len":int,"acc":str,"value":int|None}]
        # ITM 多通道 / 事件
        self.chan_text = {}     # port -> deque(str)
        self.chan_queues = {}   # port -> set(asyncio.Queue)
        self.event_port = 2     # 事件协议端口（type 1B + arg 4B）
        self.evt_state = 0      # 0=want_type 1=want_arg
        self.evt_type = 0
        self.evt_desync = 0
        self.stamp_drops = 0    # 两 ts 之间多事件时只给最后一个精确定时
        self.events = deque(maxlen=2000)  # (gtc, type, arg)
        # 反汇编缓存
        self.disasm = None      # {"elf","mtime","funcs","rows","addrs"}
        self.disasm_src = None  # -S 源码交错变体
        # 变量 watch
        self.watches = []       # [{"name","addr","size","fmt","series"}]
        self.watch_ms = 50      # watch 采样周期（默认 50ms 配 20fps 推送）

    def sym_lookup(self, addr):
        if not self.syms:
            return "??"
        lo, hi, best = 0, len(self.syms) - 1, None
        while lo <= hi:
            mid = (lo + hi) // 2
            if self.syms[mid][0] <= addr:
                best = self.syms[mid]
                lo = mid + 1
            else:
                hi = mid - 1
        if not best:
            return "??"
        base, sz, name = best
        off = addr - base
        return name if off == 0 else f"{name}+0x{off:x}"


ST = State()


# ---------------------------------------------------------------- ITM 解析
class ItmParser:
    """缓冲式 ITM/DWT 流解析（事实语义均在板上实测钉死）：
      * ts 包跟在它计时的包 *后面*，payload 为距上一 ts 的 GTC 差值，
        GTC = HCLK = 72MHz（71997t == STK_LOAD+1 == 1ms 验证）
      * 异常/PC 包后各跟一个 ts；包头 bits[1:0] 是长度码 {1:1B,2:2B,3:4B}
      * 目标侧 ITM 有 ~0.2%/字节 的自发丢包 -> 必须能重同步"""

    ANCHORS = (b"\x0e", b"\x17", b"\x15", b"\x01", b"\xc0")

    def __init__(self, st):
        self.st = st
        self.buf = bytearray()

    def feed(self, data):
        self.buf += data
        i = self._parse()
        del self.buf[:i]

    def _resync(self, i):
        st = self.st
        st.resyncs += 1
        best = len(self.buf)
        for pat in self.ANCHORS:
            j = self.buf.find(pat, i + 1, i + 256)
            if 0 <= j < best:
                best = j
        return best

    def _parse(self):
        st = self.st
        buf = self.buf
        n = len(buf)
        i = 0
        while i < n:
            c = buf[i]
            # ---- 快路径：DWT 硬件源 PC 采样包（0x15/0x17，占流量 95%）----
            # 定长 1+4 字节，批量消费；不走下面逐字节的 if/elif 链
            # （PC采样+异常同开时 Python 逐字节就是 CPU 瓶颈——实测卡 UI）
            if c == 0x17 or c == 0x15:
                if c == 0x15:                  # sleep 变体无 payload
                    st.pc_sleep += 1; i += 1; continue
                if i + 5 <= n:
                    st.pc_total += 1
                    pc = buf[i+1] | (buf[i+2] << 8) | (buf[i+3] << 16) | (buf[i+4] << 24)
                    if not (pc & 1):           # 偶地址 = 指令位置
                        st.pc_hist[pc] = st.pc_hist.get(pc, 0) + 1
                    i += 5
                    continue
                # 不完整（缓冲尾）→ 走慢路径等下一批
            # ---- 时间戳：header 0xC0-0xFF & low nibble 0，payload 7bit 累加
            if (c & 0x0F) == 0 and c >= 0xC0:
                j = i + 1
                val = shift = 0
                done = False
                while j < n and j - i <= 5:
                    b = buf[j]
                    val |= (b & 0x7F) << shift
                    shift += 7
                    j += 1
                    if not b & 0x80:
                        done = True
                        break
                if done:
                    st.gtc += val
                    self._stamp(st.gtc)
                    i = j
                elif j >= n:
                    return i  # 缓冲不足，等下一批数据
                else:
                    i = self._resync(i)
                continue
            if c == 0x70:
                st.overflows += 1
                i += 1
                continue
            if c == 0x15:  # PC 采样 sleep 变体（无 payload）
                st.pc_sleep += 1
                i += 1
                continue
            if c == 0x00 or (c & 0x0F) in (0x04, 0x08, 0x0C):
                st.resyncs += 1  # sync 序列 / reserved / extension
                i = self._resync(i) if c == 0x00 else i + 1
                continue
            size = SIZE.get(c & 3)
            if size is None:
                i = self._resync(i)
                continue
            if i + 1 + size > n:
                return i  # 包不完整
            payload = buf[i + 1:i + 1 + size]
            if c & 0x04:  # DWT 硬件源
                typ = c >> 3
                if typ == 2 and size == 4:  # PC 采样
                    pc = int.from_bytes(payload, "little")
                    st.pc_hist[pc] = st.pc_hist.get(pc, 0) + 1
                    st.pc_total += 1
                elif typ == 1 and size == 2:  # 异常跟踪
                    v = int.from_bytes(payload, "little")
                    kind = {1: "entry", 2: "exit", 3: "ret"}.get(v >> 12)
                    if kind:
                        st.exc_events += 1
                        _k = (kind, v & 0x1FF)
                        st.exc_diag[_k] = st.exc_diag.get(_k, 0) + 1
                        st._awaiting.append(("exc", kind, v & 0x1FF))
                        # 中断计数在 parse 侧直接累加（不依赖 _stamp 配时——
                        # 1kHz SysTick 的 entry 总被 exit/ret 挤丢 = n 恒 0，
                        # 同开 PC 采样后时间戳频率变化才"看起来有了"）
                        if kind in ("entry", "exit"):
                            exc_n = v & 0x1FF
                            if exc_n > 1:
                                d = st.exc.get(exc_n)
                                if d is None:
                                    d = st.exc[exc_n] = {
                                        "n": 0, "n_exit": 0,
                                        "h_sum": 0, "h_n": 0,
                                        "h_max": 0, "t_sum": 0, "t_n": 0,
                                        "p_sum": 0, "p_n": 0,
                                        "last_entry": None, "p_est": None}
                                if kind == "entry":
                                    d["n"] += 1
                                else:
                                    d["n_exit"] += 1
                                    if d["n"] < d["n_exit"]:
                                        d["n"] = d["n_exit"]  # entry 丢包时用 exit
            elif c >> 3 == 0:  # SWIT port0 文本（printf 控制台）
                try:
                    s = payload.decode("ascii")
                except UnicodeDecodeError:
                    s = ""
                if all(ch >= " " or ch in "\r\n\t" for ch in s):
                    st.text.extend(s)
                    for q in list(st.con_queues):
                        try:
                            q.put_nowait(s)
                        except asyncio.QueueFull:
                            pass
            else:  # 其余 stimulus port（1-31）
                port = c >> 3
                if port == st.event_port:
                    # 事件协议：一条记录 = 1B type 包 + 4B arg 包（同口连发，
                    # 定长记录抗整包丢失；arg 丢后跟的 1B 视为下一条的 type）
                    if st.evt_state == 0:
                        if size == 1 and payload[0] < 64:
                            st.evt_type = payload[0]
                            st.evt_state = 1
                        else:
                            st.evt_desync += 1
                    elif size == 4:
                        st._awaiting.append(
                            ("evt", st.evt_type,
                             int.from_bytes(payload, "little")))
                        st.evt_state = 0
                    elif size == 1 and payload[0] < 64:
                        st.evt_desync += 1
                        st.evt_type = payload[0]  # 留在等 arg
                    else:
                        st.evt_desync += 1
                        st.evt_state = 0
                else:
                    try:
                        s = payload.decode("ascii")
                    except UnicodeDecodeError:
                        s = ""
                    if all(ch >= " " or ch in "\r\n\t" for ch in s):
                        dq = st.chan_text.get(port)
                        if dq is None:
                            dq = st.chan_text[port] = deque(maxlen=20000)
                        dq.extend(s)
                        for q in list(st.chan_queues.get(port, ())):
                            try:
                                q.put_nowait(s)
                            except asyncio.QueueFull:
                                pass
            i += 1 + size
        return i

    def _stamp(self, gtc):
        """ts 到达：给它前面最近的未配时项定时（异常或 ITM 事件）。
        两个 ts 之间若有多个待配项，只有最后一个拿到精确定时，其余
        计 stamp_drops 丢弃——协议粒度如此，异常与事件流同时开时
        时间分辨率退化到 ts 间隔。"""
        st = self.st
        if not st._awaiting:
            return
        if len(st._awaiting) > 1:
            st.stamp_drops += len(st._awaiting) - 1
        item = st._awaiting.pop()
        if item[0] == "evt":
            st.events.append((gtc, item[1], item[2]))
            return
        kind, exc = item[1], item[2]
        st.exc_recent.append((gtc, kind, exc))
        if kind == "ret":  # 返回线程：exc 字段恒 0，线程间隙用它全局配
            if st.last_exit is not None:
                st.r_sum += gtc - st.last_exit
                st.r_n += 1
            st.last_ret = gtc
            return
        if exc > 63:
            st.exc_mispaired += 1
            return
        d = st.exc.get(exc)
        if kind == "entry":
            if d is None:
                d = st.exc[exc] = {"n": 0, "h_sum": 0, "h_n": 0, "h_max": 0,
                                   "t_sum": 0, "t_n": 0, "p_sum": 0, "p_n": 0,
                                   "last_entry": None, "p_est": None}
            # n 已在 parse 侧计数，此处不重复
            if d["last_entry"] is not None:
                p = gtc - d["last_entry"]
                d["p_sum"] += p
                d["p_n"] += 1
                if 0 < p < (1 << 31):
                    d["p_est"] = p
            if st.last_ret is not None:
                d["t_sum"] += gtc - st.last_ret
                d["t_n"] += 1
            d["last_entry"] = gtc
        elif kind == "exit":
            if d and d["last_entry"] is not None:
                h = gtc - d["last_entry"]
                # 丢 entry 包时 exit 会撞上一个周期的 entry（~一个周期），
                # 用滚动周期估计的 1/4 做自适应上限
                thr = d["p_est"] // 4 if d.get("p_est") else 2_000_000
                if 0 <= h < thr:
                    d["h_sum"] += h
                    d["h_n"] += 1
                    d["h_max"] = max(d["h_max"], h)
                else:
                    st.exc_mispaired += 1
            st.last_exit = gtc


PARSER = ItmParser(ST)


# ---------------------------------------------------------------- jtag_tool 二进制客户端
# 板上 jtag_tool --serve 命令口（5555）包协议：
#   [seq:1][cmd:1][len:2 LE][payload]；响应 cmd=req|0x80，错误 0x7F+文本。
#   严格一问一答（锁内单飞），无文本解析/标记/回显——比 telnet 干净一个量级。
# SWO 流口 5556 直收原始字节（swo_loop）。
BIN_PING, BIN_CMD, BIN_HALTINFO, BIN_HALT, BIN_RESUME, BIN_STEP = 1, 2, 3, 4, 5, 6
BIN_REG_RD, BIN_REG_WR, BIN_MEM_RD, BIN_MEM_WR = 7, 8, 9, 0xA
BIN_BP_ADD, BIN_BP_DEL, BIN_WP_ADD, BIN_WP_DEL, BIN_BPS = 0xB, 0xC, 0xD, 0xE, 0xF
BIN_SWO_TPIU, BIN_SWO_STAT, BIN_REPROBE = 0x10, 0x11, 0x12
BIN_ERR = 0x7F
# 寄存器 sel 序（r0-r12, sp, lr, pc, xpsr, msp, psp, primask, basepri, faultmask, control）
REG_SELS = bytes([*range(13), 13, 14, 15, 0x10, 0x11, 0x12, 0x14, 0x15, 0x16, 0x17])
REG_NAMES = ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12",
             "sp","lr","pc","xpsr","msp","psp","primask","basepri","faultmask",
             "control"]
REASON_NAMES = {0: "", 1: "debug-request", 2: "breakpoint", 3: "watchpoint",
                4: "vector-catch", 5: "external"}


class Ocd:
    def __init__(self):
        self.r = self.w = None
        self.lock = asyncio.Lock()
        self._seq = 0
        self._eio_streak = 0

    async def _drop(self):
        if self.w:
            try:
                self.w.close()
            except Exception:
                pass
        self.r = self.w = None

    async def _ensure(self):
        """假定已持锁。建连即配 SWO（幂等；板侧服务可能刚重启丢配置）。"""
        if self.w is not None and not self.w.is_closing():
            return
        await self._drop()
        self.r, self.w = await open_conn_ka(board_addr(BOARD_HOST), OCD_PORT)
        try:
            await self._xchg_locked(
                BIN_SWO_TPIU,
                struct.pack("<II", ST.swo_traceclk, ST.swo_baud), 8.0)
            # swo_tpiu 安全序列会停 DWT。此处已持锁，必须直写重放
            # （set_trace→mww→_xchg 会二次抢非重入锁 = 自死锁）
            v = CYCCNTENA | (PCSAMPLENA if ST.pc_on else 0) \
                | (EXCTRCENA if ST.exc_on else 0)
            await self._xchg_locked(
                BIN_MEM_WR,
                struct.pack("<IBH", DWT_CTRL, 4, 1) + struct.pack("<I", v))
        except Exception:
            pass

    async def _xchg(self, cmd, payload=b"", timeout=8.0):
        """公共入口：持锁一问一答；错误抛 RuntimeError。"""
        async with self.lock:
            return await self._xchg_locked(cmd, payload, timeout)

    async def _xchg_locked(self, cmd, payload=b"", timeout=8.0):
        for attempt in range(2):
            try:
                await self._ensure()
                self._seq = (self._seq + 1) & 0xFF
                self.w.write(bytes((self._seq, cmd, len(payload) & 0xFF,
                                    len(payload) >> 8)) + payload)
                await self.w.drain()
                hdr = await asyncio.wait_for(self.r.readexactly(4), timeout)
                rlen = hdr[2] | (hdr[3] << 8)
                body = (await asyncio.wait_for(
                    self.r.readexactly(rlen), timeout)
                    if rlen else b"")
                ST.ocd_ok = True
                if hdr[1] == BIN_ERR:
                    self._eio_streak += 1
                    txt = body.decode(errors="replace") or "jtag_tool 错误"
                    if self._eio_streak >= 5:   # 连续命令级失败=target 链路死
                        self._eio_streak = 0    # 让板侧重探（幂等，~百 ms）
                        try:
                            await self._xchg_locked(BIN_REPROBE)
                        except Exception:
                            pass
                    raise RuntimeError(txt)
                self._eio_streak = 0
                return body
            except RuntimeError:
                raise                      # 业务错误：链路没坏，直接抛
            except Exception:
                ST.ocd_ok = False
                await self._drop()
                await asyncio.sleep(0.3)
        raise RuntimeError("jtag_tool 链路无响应")

    # ---------- 域方法 ----------
    async def cmd(self, line, timeout=8.0):
        """文本命令（raw 命令箱）——仅此一处走文本层。"""
        out = await self._xchg(BIN_CMD, line.encode()[:200], timeout)
        ST.ocd_ok = True
        return out.decode(errors="replace")

    async def cmd_batch(self, lines, timeout=8.0):
        lines = [l for l in lines if l]
        if not lines:
            return []
        return [await self.cmd(l, timeout) for l in lines]

    async def haltinfo(self):
        """-> (state, reason_str, pc|None)；state: running|halted。"""
        b = await self._xchg(BIN_HALTINFO)
        state = "halted" if b[0] else "running"
        reason = REASON_NAMES.get(b[1], "")
        pc = struct.unpack_from("<I", b, 2)[0] if len(b) >= 6 else None
        ST.ocd_ok = True
        return state, reason, pc

    async def halt(self):
        b = await self._xchg(BIN_HALT)
        return struct.unpack("<I", b)[0] if len(b) == 4 else None

    async def resume(self):
        await self._xchg(BIN_RESUME)

    async def step(self, n=1):
        b = await self._xchg(BIN_STEP, bytes([max(1, min(16, n))]), 20.0)
        return struct.unpack("<I", b)[0] if len(b) == 4 else None

    async def regs(self, sels=REG_SELS):
        """-> dict name->int（一次包读全部核寄存器）。"""
        b = await self._xchg(BIN_REG_RD, sels)
        vals = struct.unpack("<%dI" % (len(b) // 4), b[:len(b) // 4 * 4])
        return dict(zip(REG_NAMES[:len(vals)], vals))

    async def mem_read(self, addr, count, width=4):
        """-> [int]（宽度 width 字节，LE；width=8 由板端两条 32 位读合并）。"""
        if width == 8:
            count = max(1, min(512, count))
        b = await self._xchg(BIN_MEM_RD,
                             struct.pack("<IBH", addr, width,
                                         max(1, min(1024, count))))
        per = width
        n = len(b) // per
        return [int.from_bytes(b[i * per:(i + 1) * per], "little")
                for i in range(n)][:count]

    async def mem_write(self, addr, val, width=4):
        data = int(val).to_bytes(width, "little")
        await self._xchg(BIN_MEM_WR,
                         struct.pack("<IBH", addr, width, 1) + data)
        return ""

    async def mww(self, addr, val):
        await self.mem_write(addr, val, 4)

    async def mdw(self, addr, count=1):
        return await self.mem_read(addr, count, 4)

    async def bp_add(self, addr, ln=2):
        await self._xchg(BIN_BP_ADD, struct.pack("<IB", addr, ln))

    async def bp_del(self, addr=None):
        await self._xchg(BIN_BP_DEL,
                         struct.pack("<I", 0xFFFFFFFF if addr is None
                                     else addr))

    async def wp_add(self, addr, ln, acc):
        await self._xchg(BIN_WP_ADD,
                         struct.pack("<IIB", addr, ln,
                                     {"r": 5, "w": 6, "a": 7}[acc]))

    async def wp_del(self, addr=None):
        await self._xchg(BIN_WP_DEL,
                         struct.pack("<I", 0xFFFFFFFF if addr is None
                                     else addr))

    async def bps(self):
        """-> (bps:[(addr,len)], wps:[(addr,len,acc_char)])。"""
        b = await self._xchg(BIN_BPS)
        nb = b[0]
        i, bps = 1, []
        for _ in range(nb):
            bps.append((struct.unpack_from("<I", b, i)[0], b[i + 4]))
            i += 5
        nw = b[i]
        i += 1
        wps = []
        for _ in range(nw):
            wps.append((struct.unpack_from("<I", b, i)[0],
                        struct.unpack_from("<I", b, i + 4)[0],
                        {5: "r", 6: "w", 7: "a"}.get(b[i + 8], "?")))
            i += 9
        return bps, wps

    async def swo_tpiu(self, traceclk, baud):
        b = await self._xchg(BIN_SWO_TPIU, struct.pack("<II", traceclk, baud))
        # 板侧安全序列会停 DWT 产出：按当前 pc/exc 开关重放
        try:
            await self.set_trace()
        except Exception:
            pass
        return struct.unpack("<I", b)[0] if len(b) == 4 else 0

    async def swo_stat(self):
        b = await self._xchg(BIN_SWO_STAT)
        return (b[0] | (b[1] << 8), b[2], b[3])   # cnt, ovr, fe

    async def set_trace(self, pc=None, exc=None):
        v = CYCCNTENA
        if pc is not None:
            ST.pc_on = pc
            ST.pc_hist, ST.pc_total, ST.pc_t0 = {}, 0, time.time()
        if exc is not None:
            ST.exc_on = exc
            ST.exc, ST.exc_events = {}, 0
        if ST.pc_on:
            v |= PCSAMPLENA
        if ST.exc_on:
            v |= EXCTRCENA
        await self.mww(DWT_CTRL, v)
        return v


OCD = Ocd()


# ---------------------------------------------------------------- 目标状态/寄存器/断点
async def tgt_probe():
    """haltinfo：更新 ST.tgt_state/halt_reason/halt_pc（DFSR 读清语义：
    每次轮询只看新事件，停住后 reason 保持到 resume）。"""
    try:
        state, reason, pc = await OCD.haltinfo()
    except Exception:
        return ST.tgt_state
    ST.tgt_state = state
    if state == "running":
        ST.halt_reason, ST.halt_pc = "", None
    else:
        if reason:
            ST.halt_reason = reason
        if pc is not None:
            ST.halt_pc = pc
    return ST.tgt_state


async def refresh_regs():
    try:
        regs = await OCD.regs()
        if regs:
            ST.regs = regs
    except Exception:
        pass
    return ST.regs


async def refresh_bps():
    try:
        bps, wps = await OCD.bps()
        ST.bps = [{"addr": a, "len": ln, "hw": True} for a, ln in bps]
        ST.wps = [{"addr": a, "len": ln, "acc": acc} for a, ln, acc in wps]
    except Exception:
        pass
    return ST.bps, ST.wps


def resolve_sym(text):
    """'0x..' / 十进制 / 符号名 -> (addr, size)；解析失败 (None, 0)。"""
    t = str(text or "").strip()
    if not t:
        return None, 0
    try:
        return int(t, 0), 4
    except ValueError:
        pass
    return ST.sym_by_name.get(t, (None, 0))


async def tgt_loop():
    while True:
        try:
            if await tgt_probe() == "halted":
                await refresh_regs()
                await asyncio.sleep(0.25)
            else:
                ST.regs = {}
                await asyncio.sleep(1.0)
        except Exception:
            await asyncio.sleep(1.0)


# ---------------------------------------------------------------- 反汇编（host objdump）
DISASM_RE_FUNC = re.compile(r"^([0-9A-Fa-f]+) <(.+)>:$")
# objdump 指令行固定为 "addr:\t字节域\t助记符"，字节域 16 位指令无内嵌
# 空格（"495c"）、32 位为半字空格分隔（"f8df 1294"），不能靠空格正则
DISASM_RE_INSN = re.compile(r"^\s*([0-9A-Fa-f]+):\t(.*)$")
OBJDUMP_FALLBACK = ("/home/victor/Arise2/toolchains/"
                    "gcc-arm-none-eabi-9-2019-q4-major/bin/arm-none-eabi-objdump",)


def objdump_exe():
    p = os.environ.get("OBJDUMP")
    if p and os.access(p, os.X_OK):
        return p
    p = shutil.which("arm-none-eabi-objdump")
    if p:
        return p
    for p in OBJDUMP_FALLBACK:
        if os.access(p, os.X_OK):
            return p
    return None


def build_disasm(elf, src):
    """objdump -d/-S 一次全量跑（固件小），解析为
    {"elf","mtime","funcs":[(addr,end,name)],"rows":[...]}；
    rows: ("f",name,addr) / ("i",addr,bytes,text) / ("s",源码行)。"""
    exe = objdump_exe()
    if not exe:
        return None, "arm-none-eabi-objdump 未找到（OBJDUMP 环境变量可指定路径）"
    cmd = [exe] + (["-S"] if src else []) + ["-d", elf]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
    except Exception as e:
        return None, f"objdump 执行失败: {e!r}"
    if r.returncode != 0:
        return None, (r.stderr or "objdump 失败").strip()[-300:]
    funcs, rows = [], []
    cur = None
    for ln in r.stdout.splitlines():
        m = DISASM_RE_FUNC.match(ln)
        if m:
            if cur is not None:
                cur[1] = int(m.group(1), 16)
            cur = [int(m.group(1), 16), None, m.group(2)]
            funcs.append(cur)
            rows.append(("f", m.group(2), cur[0]))
            continue
        m = DISASM_RE_INSN.match(ln)
        if m:
            rest = m.group(2)
            parts = rest.split("\t", 1)
            raw = parts[0].strip()
            if len(parts) == 2 and raw and all(
                    c in "0123456789abcdefABCDEF " for c in raw):
                rows.append(("i", int(m.group(1), 16), raw, parts[1].strip()))
            else:
                rows.append(("i", int(m.group(1), 16), "", rest.strip()))
            continue
        s = ln.rstrip()
        if (s and not s.startswith("Disassembly of section")
                and "file format elf" not in s):
            rows.append(("s", s))
    if cur is not None and cur[1] is None:
        cur[1] = max((r[1] for r in rows if r[0] == "i"),
                     default=cur[0]) + 4
    try:
        mtime = os.path.getmtime(elf)
    except OSError:
        mtime = 0
    return {"elf": elf, "mtime": mtime, "funcs": [tuple(f) for f in funcs],
            "rows": rows}, None


async def ensure_disasm(src=False):
    cache = ST.disasm_src if src else ST.disasm
    try:
        mtime = os.path.getmtime(ST.elf_path)
    except OSError:
        return None, f"ELF 不存在: {ST.elf_path}"
    if cache and cache["elf"] == ST.elf_path and cache["mtime"] == mtime:
        return cache, None
    d, err = await asyncio.to_thread(build_disasm, ST.elf_path, src)
    if d:
        if src:
            ST.disasm_src = d
        else:
            ST.disasm = d
        return d, None
    return None, err


def disasm_window(d, addr=None, name=None):
    """取一个函数窗口的 rows：按名字或包含 addr 的函数定位。
    返回 (func_meta, rows_slice)，未命中时取最近函数。"""
    funcs = d["funcs"]
    if not funcs:
        return None, []
    fi = None
    if name:
        for k, f in enumerate(funcs):
            if f[2] == name:
                fi = k
                break
    if fi is None and addr is not None:
        starts = [f[0] for f in funcs]
        fi = max(0, bisect.bisect_right(starts, addr) - 1)
    fi = 0 if fi is None else fi
    f = funcs[fi]
    out, inwin, cnt = [], False, 0
    for r in d["rows"]:
        if r[0] == "f":
            inwin = r[1] == f[2] and r[2] == f[0]
            continue
        if inwin:
            out.append(r)
            cnt += 1
            if cnt >= 3000:
                break
    return f, out


# ---------------------------------------------------------------- 变量 watch
def watch_setfmt(name, fmt):
    """行内改格式：只换解释（f32/i32/hex 互换不动提取）；u16/u8 连子字
    提取宽度一起换。"""
    if fmt not in ("u32", "i32", "hex", "u16", "i16", "u8", "i8",
                   "f32", "u64", "i64", "f64"):
        return False, "bad fmt"
    for w in ST.watches:
        if w["name"] == name:
            w["fmt"] = fmt
            w["size"] = {"u16": 2, "i16": 2, "u8": 1, "i8": 1}.get(fmt, 4)
            return True, ""
    return False, f"未找到: {name}"


def watch_setwin(name, win):
    """变量分配到波形窗口 0=不显示 / 1-4（多窗口各自 Y 量程）。"""
    try:
        win = max(0, min(4, int(win)))
    except (TypeError, ValueError):
        return False, "bad win"
    for w in ST.watches:
        if w["name"] == name:
            w["win"] = win
            return True, ""
    return False, f"未找到: {name}"


def watch_add(name, fmt, win=1):
    """加 watch（符号名或 0x 原始地址）。>4B 符号（数组/结构体）监控首字。
    win = 波形窗口号 1-4。返回 (ok, err)。"""
    name = str(name or "").strip()
    fmt = str(fmt or "u32")
    try:
        win = max(0, min(4, int(win)))
    except (TypeError, ValueError):
        win = 1
    SIZE_MAP = {"u16": 2, "i16": 2, "u8": 1, "i8": 1,
                "u64": 8, "i64": 8, "f64": 8}
    ent = ST.sym_by_name.get(name)
    if ent:
        addr, size, disp = ent[0], ent[1], name
        if fmt in SIZE_MAP:
            size = SIZE_MAP[fmt]  # fmt 覆盖符号大小
        elif size > 8:
            size = 8              # 数组/结构体：先看前 8 字节
    else:
        try:
            addr = int(name, 0)
        except ValueError:
            return False, f"符号未找到: {name}"
        size = SIZE_MAP.get(fmt, 4)
        disp = f"0x{addr:08x}"
    if not any(w["addr"] == addr and w["name"] == disp for w in ST.watches):
        ST.watches.append({"name": disp, "addr": addr, "size": size,
                           "fmt": fmt, "win": win,
                           "series": deque(maxlen=600)})
    return True, ""


async def watch_loop():
    while True:
        try:
            if ST.watches and ST.tgt_state != "unknown":
                ws = sorted(ST.watches, key=lambda w: w["addr"])
                segs = []
                for w in ws:
                    b = w["addr"] & ~3
                    if segs and b < segs[-1][0] + segs[-1][1] * 4 + 64:
                        need = (b + 4 - segs[-1][0]) // 4
                        if need > segs[-1][1]:
                            segs[-1][1] = need
                    else:
                        segs.append([b, 1])
                words, now = {}, time.time()
                for b, n in segs:
                    try:
                        vals = await OCD.mem_read(b, n, 4)
                    except Exception:
                        vals = []
                    for k, v in enumerate(vals):
                        words[b + 4 * k] = v
                for w in ST.watches:
                    if w["size"] == 8:
                        # 8 字节：合并两个相邻 32 位字（小端低字在前）
                        base = w["addr"] & ~7
                        word = (words.get(base) or 0) | \
                               ((words.get(base + 4) or 0) << 32)
                    else:
                        # 1/2/4 字节：只取对应的 32 位字
                        base = w["addr"] & ~3
                        word = words.get(base)
                        if word is not None and w["size"] < 4:
                            sh = (w["addr"] & 3) * 8
                            word = (word >> sh) & ((1 << (w["size"] * 8)) - 1)
                    w["series"].append((now, word))
                    w["n"] = w.get("n", 0) + 1
        except Exception:
            pass
        await asyncio.sleep(max(0.05, ST.watch_ms / 1000.0))


# ---------------------------------------------------------------- 后台任务
async def open_conn_ka(host, port):
    """带 TCP keepalive 的连接：板子双网卡（IP 漂移）时旧连接会被网络
    静默丢弃（无 FIN/RST），read() 永远等下去——keepalive 让死连接在
    ~10s 内报错触发重连。"""
    loop = asyncio.get_running_loop()
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
    for opt, val in ((socket.TCP_KEEPIDLE, 5), (socket.TCP_KEEPINTVL, 2),
                     (socket.TCP_KEEPCNT, 3)):
        try:
            sock.setsockopt(socket.IPPROTO_TCP, opt, val)
        except (AttributeError, OSError):
            pass
    sock.setblocking(False)
    try:
        await loop.sock_connect(sock, (host, port))
    except Exception:
        sock.close()
        raise
    return await asyncio.open_connection(sock=sock)


async def swo_loop():
    while True:
        try:
            t0 = time.monotonic()
            addr = board_addr(BOARD_HOST)
            ST.swo_state = f"connecting {addr} (第{ST.swo_conn_n}次)"
            r, w = await open_conn_ka(addr, SWO_PORT)
            ST.swo_conn_n += 1
        except OSError as e:
            ST.swo_ok = False
            ST.swo_state = f"conn-fail {e!r}"
            await asyncio.sleep(1.0)
            continue
        ST.swo_ok = True
        ST.swo_state = "reading"
        try:
            while True:
                try:
                    data = await asyncio.wait_for(r.read(4096), 10.0)
                except asyncio.TimeoutError:
                    # DWT 在产流却 10s 零字节 = 目标 SWO 输出静默卡死
                    # （寄存器全对、线 idle），swo_tpiu 重配（内含 SWJ_CFG
                    # 循环）一踢即活
                    if ST.pc_on or ST.exc_on:
                        ST.swo_state = "静默>10s，重配踢活中"
                        try:
                            await OCD.swo_tpiu(ST.swo_traceclk, ST.swo_baud)
                        except Exception:
                            pass
                        ST.swo_state = "reading"
                    continue
                if not data:
                    break
                ST.swo_last_rx = time.time()
                PARSER.feed(data)
        except (ConnectionError, OSError) as e:
            ST.swo_last_err = repr(e)
        except Exception:
            # 解析器崩了也得死得大声：打全堆栈，别静默吞任务
            import traceback
            traceback.print_exc()
            ST.swo_last_err = "parser crash（栈见服务器日志）"
        finally:
            try:
                w.close()
            except Exception:
                pass
        ST.swo_ok = False
        ST.swo_state = "对端关闭，重连中"
        await asyncio.sleep(1.0)


async def dwt_loop():
    prev = None
    prev_t = 0.0
    tick = 0
    while True:
        try:
            vals = await OCD.mdw(0xE0001004, 6)
            if len(vals) == 6:
                now = time.time()
                ST.dwt_raw = vals
                if prev:
                    dt = max(now - prev_t, 1e-3)
                    dcyc = (vals[0] - prev[0]) & 0xFFFFFFFF

                    def d8(a, b):
                        return (a - b) & 0xFF

                    ST.mhz = dcyc / dt / 1e6 if dcyc < 0x8000000 else 0.0
                    ST.exc_ps = d8(vals[2], prev[2]) / dt
                    dslp = d8(vals[3], prev[3])
                    ST.sleep_pct = (min(dslp * 100.0 / dcyc, 100.0)
                                    if dcyc else 100.0)
                prev, prev_t = vals, now
            tick += 1
            if tick % 8 == 0:
                ctl = await OCD.mdw(DWT_CTRL, 1)
                if ctl:
                    ST.pc_on = bool(ctl[0] & PCSAMPLENA)
                    ST.exc_on = bool(ctl[0] & EXCTRCENA)
        except Exception:
            pass
        await asyncio.sleep(0.25)


# ---------------------------------------------------------------- HTTP
def json_resp(writer, obj, status=200):
    body = json.dumps(obj, ensure_ascii=False).encode()
    writer.write(
        f"HTTP/1.0 {status} OK\r\nContent-Type: application/json; "
        f"charset=utf-8\r\nContent-Length: {len(body)}\r\n"
        "Connection: close\r\n\r\n".encode() + body)


async def read_req(reader):
    line = await reader.readline()
    parts = line.decode(errors="replace").split()
    if len(parts) < 2:
        return None, None, {}
    method, path = parts[0], parts[1]
    headers = {}
    while True:
        h = await reader.readline()
        if h in (b"\r\n", b"\n", b""):
            break
        k, _, v = h.decode(errors="replace").partition(":")
        headers[k.strip().lower()] = v.strip()
    body = b""
    if headers.get("content-length"):
        body = await reader.readexactly(int(headers["content-length"]))
    return method, path, headers, json.loads(body) if body else {}


# ---------------------------------------------------------------- WebSocket（stdlib）
# 单页 UI 的实时通道：一条 /ws 长连接——服务端每 400ms 推
# {t:push, status, tab, data}（data 为当前订阅 tab 的载荷），控制台文本
# 以 {t:con} 实时帧转发；请求-响应走同一连接，带 id 关联。HTTP 端点
# 保留（curl 验证 / mock 回归用）。
WS_GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"


def ws_encode(text):
    payload = text.encode() if isinstance(text, str) else text
    n = len(payload)
    if n < 126:
        hdr = struct.pack("!BB", 0x81, n)
    elif n < 65536:
        hdr = struct.pack("!BBH", 0x81, 126, n)
    else:
        hdr = struct.pack("!BBQ", 0x81, 127, n)
    return hdr + payload


async def ws_handshake(writer, headers):
    key = headers.get("sec-websocket-key")
    if not key:
        return False
    acc = base64.b64encode(
        hashlib.sha1((key + WS_GUID).encode()).digest()).decode()
    writer.write(
        b"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\n"
        b"Connection: Upgrade\r\n"
        + f"Sec-WebSocket-Accept: {acc}\r\n\r\n".encode())
    await writer.drain()
    return True


async def ws_read_msg(reader, writer):
    """读一条完整消息（text 帧，含分片）；ping 回 pong；close 返回 None。"""
    msg = b""
    while True:
        h = await reader.readexactly(2)
        fin, op = h[0] & 0x80, h[0] & 0x0F
        masked, ln = h[1] & 0x80, h[1] & 0x7F
        if ln == 126:
            ln = struct.unpack("!H", await reader.readexactly(2))[0]
        elif ln == 127:
            ln = struct.unpack("!Q", await reader.readexactly(8))[0]
        mask = await reader.readexactly(4) if masked else b""
        data = await reader.readexactly(ln) if ln else b""
        if masked and data:
            data = bytes(b ^ mask[i & 3] for i, b in enumerate(data))
        if op == 8:
            return None
        if op == 9:                      # ping -> pong
            writer.write(b"\x8a" + bytes([len(data)]) + data)
            await writer.drain()
            continue
        if op in (0x0, 0x1, 0x2):
            msg += data
            if fin:
                return msg


def ws_sub_con(sess, port):
    """把会话的控制台订阅切到 port 通道（换队列接入对应扇出）。"""
    old = sess.pop("con_q", None)
    if old is not None:
        if sess["conport"] == 0:
            ST.con_queues.discard(old)
        else:
            qs = ST.chan_queues.get(sess["conport"])
            if qs is not None:
                qs.discard(old)
    q = asyncio.Queue(maxsize=2000)
    sess["con_q"] = q
    sess["conport"] = port
    if port == 0:
        ST.con_queues.add(q)
    else:
        ST.chan_queues.setdefault(port, set()).add(q)


async def ws_con_forwarder(sess):
    """控制台实时帧：con_q -> {t:con,s:...}（小批量合并）。"""
    q = sess["con_q"]
    try:
        while True:
            chunk = await q.get()
            parts = [chunk]
            while len(parts) < 16:
                try:
                    parts.append(q.get_nowait())
                except asyncio.QueueEmpty:
                    break
            sess["q"].put_nowait({"t": "con", "s": "".join(parts)})
    except asyncio.CancelledError:
        pass
    except Exception:
        pass


async def ws_pusher(sess):
    """周期推送：status + 当前 tab 载荷（120ms ≈ 8fps，丝滑的关键）。"""
    q = sess["q"]
    print("[PUSHER-START]", flush=True)
    try:
        while True:
            await asyncio.sleep(0.05)
            try:
                st = api_status()
            except Exception as _e:
                print(f"[push-status-err] {_e!r}", flush=True)
                continue
            tab = sess["tab"]
            payload = {"t": "push", "status": st, "tab": tab}
            try:
                if tab == "prof":
                    payload["data"] = api_pcstats()
                elif tab == "exc":
                    payload["data"] = api_excstats()
                elif tab == "tl2":
                    payload["data"] = api_events()
                elif tab == "debug":
                    payload["data"] = {
                        "state": st["tgt_state"],
                        "reason": st["halt_reason"],
                        "pc": (f"0x{ST.halt_pc:08x}"
                               if ST.halt_pc is not None else None),
                        "regs": {k: f"0x{v:08x}"
                                 for k, v in ST.regs.items()}}
                elif tab == "watch":
                    # 增量推送：绝对计数游标（deque 打满后 len 不再增长，
                    # 按 len 切片会永久发空 = 波形 30s 后冻结的根因）
                    ws = ST.watches
                    sig = ",".join(f"{w['name']}|{w['fmt']}|{w.get('win', 1)}"
                                   for w in ws)
                    cur = sess.setdefault("wcur", {"sig": None, "sent": {}})
                    full = cur["sig"] != sig
                    if full:
                        cur["sig"] = sig
                        cur["sent"] = {}
                    watches = []
                    for w in ws:
                        n_abs = w.get("n", len(w["series"]))
                        sent = cur["sent"].get(w["name"], 0)
                        ser = w["series"]
                        lag = n_abs - sent
                        if full or lag > len(ser) or lag < 0:
                            pts = [[round(t, 3), v]
                                   for t, v in ser]
                            full_w = True
                        else:
                            pts = [[round(t, 3), v]
                                   for t, v in list(ser)[len(ser) - lag:]] \
                                if lag else []
                            full_w = False
                        cur["sent"][w["name"]] = n_abs
                        watches.append({
                            "name": w["name"],
                            "addr": f"0x{w['addr']:08x}",
                            "size": w["size"], "fmt": w["fmt"],
                            "win": w.get("win", 1),
                            "full": full_w, "pts": pts})
                    payload["data"] = {"watches": watches}
                elif tab == "dwt":
                    payload["data"] = {
                        "mhz": round(ST.mhz, 2),
                        "exc_ps": round(ST.exc_ps, 1),
                        "sleep_pct": round(ST.sleep_pct, 1),
                        "raw": {"cyc": f"0x{ST.dwt_raw[0]:08x}",
                                "cpi": ST.dwt_raw[1], "exc": ST.dwt_raw[2],
                                "slp": ST.dwt_raw[3], "lsu": ST.dwt_raw[4],
                                "fold": ST.dwt_raw[5]}}
            except Exception:
                pass
            try:
                _w = sess.get("_writer")
                if _w and not _w.is_closing():
                    _w.write(ws_encode(json.dumps(payload, ensure_ascii=False)))
            except Exception as _e:
                print(f"[push-direct-err] {_e!r}", flush=True)
                break
    except asyncio.CancelledError:
        pass


async def ws_dispatch(sess, m):
    t = m.get("t", "")
    mid = m.get("id")

    def reply(obj):
        if mid is not None:
            obj["id"] = mid
            try:
                sess["q"].put_nowait(obj)
            except asyncio.QueueFull:
                pass

    if t == "tab":
        sess["tab"] = str(m.get("v", "console"))
    elif t == "conport":
        ws_sub_con(sess, max(0, min(31, int(m.get("v", 0)))))
    elif t == "conback":
        port = max(0, min(31, int(m.get("v", 0))))
        buf = ST.text if port == 0 else ST.chan_text.get(port)
        reply({"t": "conback", "s": "".join(buf)[-6000:] if buf else ""})
    elif t == "cmd":
        reply({"t": "resp", "out": (await OCD.cmd(
            str(m.get("line", ""))[:200], timeout=8.0)).strip()[-2000:]})
    elif t == "action":
        a = m.get("a", "")
        if a in ("halt", "resume"):
            out = await OCD.cmd(a)
        elif a == "reset":
            await OCD.mww(0xE000ED0C, 0x05FA0004)
            out = "reset (SYSRESETREQ)"
        elif a == "reset_halt":
            await OCD.mww(0xE000ED0C, 0x05FA0004)
            pc = await OCD.halt()
            out = f"halted pc=0x{pc:08x}" if pc else "halt"
        else:
            out = "bad action"
        if a in ("halt", "reset_halt"):
            await tgt_probe()
        reply({"t": "resp", "out": out.strip()[-800:]})
    elif t == "step":
        n = max(1, min(16, int(m.get("n", 1) or 1)))
        pc = await OCD.step(n)
        await tgt_probe()
        await refresh_regs()
        reply({"t": "resp", "out": f"pc=0x{pc:08x}" if pc else "",
               "state": ST.tgt_state,
               "reason": ST.halt_reason,
               "regs": {k: f"0x{v:08x}" for k, v in ST.regs.items()}})
    elif t == "ctrl":
        v = await OCD.set_trace(pc=m.get("pc"), exc=m.get("exc"))
        reply({"t": "resp", "dwt_ctrl": f"0x{v:08x}",
               "warn": ("PC 采样+异常跟踪同开会饱和 4M SWO 线"
                        ) if ST.pc_on and ST.exc_on else ""})
    elif t == "mem":
        addr, _ = resolve_sym(m.get("addr"))
        if addr is None:
            reply({"t": "resp", "error": "无法解析地址/符号"})
            return
        w = int(m.get("w", 4))
        n = max(1, min(256, int(m.get("len", 64) or 64)))
        vals = await OCD.mem_read(addr, n, w)
        bs = b"".join(v.to_bytes(w, "little") for v in vals)
        reply({"t": "resp", "addr": f"0x{addr:08x}", "w": w,
               "vals": [f"0x{v:0{2 * w}x}" for v in vals],
               "ascii": "".join(chr(b) if 32 <= b < 127 else "."
                                for b in bs)})
    elif t == "memw":
        addr, _ = resolve_sym(m.get("addr"))
        if addr is None:
            reply({"t": "resp", "error": "无法解析地址/符号"})
            return
        try:
            val = int(str(m.get("value", "")), 0)
        except ValueError:
            reply({"t": "resp", "error": "bad value"})
            return
        out = await OCD.mem_write(addr, val, int(m.get("w", 4)))
        reply({"t": "resp", "out": out.strip()[-200:]})
    elif t == "bp":
        act, kind = m.get("action", ""), m.get("kind", "bp")
        if act == "clr":
            await OCD.bp_del()
            await OCD.wp_del()
        else:
            addr, _ = resolve_sym(m.get("addr"))
            if addr is None:
                reply({"t": "resp", "error": "无法解析地址/符号"})
                return
            if kind == "bp":
                if act == "add":
                    await OCD.bp_add(addr, 4 if str(m.get("len", 2)) == "4"
                                     else 2)
                else:
                    await OCD.bp_del(addr)
            else:
                if act == "add":
                    await OCD.wp_add(addr, int(m.get("len", 4) or 4),
                                     m.get("acc", "w"))
                else:
                    await OCD.wp_del(addr)
        bps, wps = await refresh_bps()
        reply({"t": "resp", "out": "ok",
               "bps": [{"addr": f"0x{b['addr']:08x}", "len": b["len"],
                        "hw": True} for b in bps],
               "wps": [{"addr": f"0x{w['addr']:08x}", "acc": w["acc"],
                        "len": w.get("len", 4)} for w in wps]})
    elif t == "watch":
        act = m.get("action", "")
        name = str(m.get("name", "")).strip()
        if act == "add":
            ok, werr = watch_add(name, m.get("fmt", "u32"), m.get("win", 1))
            reply({"t": "resp", "ok": ok, "error": werr or None})
        elif act == "setwin":
            ok, werr = watch_setwin(name, m.get("win", 1))
            reply({"t": "resp", "ok": ok, "error": werr or None})
        elif act == "rate":
            ST.watch_ms = max(50, min(5000,
                                       int(m.get("ms", 50) or 50)))
            reply({"t": "resp", "watch_ms": ST.watch_ms})
        elif act == "setfmt":
            ok, werr = watch_setfmt(name, str(m.get("fmt", "")))
            reply({"t": "resp", "ok": ok, "error": werr or None})
        elif act == "del":
            ST.watches = [w for w in ST.watches if w["name"] != name]
            reply({"t": "resp", "count": len(ST.watches)})
        elif act == "clr":
            ST.watches = []
            reply({"t": "resp", "count": 0})
    elif t == "swocfg":
        tc = max(1_000_000, min(300_000_000,
                                 int(m.get("traceclk", 72000000) or 72000000)))
        ST.swo_traceclk = tc
        if m.get("baud"):
            ST.swo_baud = int(m["baud"])
        actual = await OCD.swo_tpiu(tc, ST.swo_baud)
        reply({"t": "resp", "traceclk": tc, "out": f"RX {actual} Hz"})
    elif t == "eventport":
        ST.event_port = max(0, min(31, int(m.get("port", 2))))
        reply({"t": "resp", "event_port": ST.event_port})
    elif t == "disfuncs":
        d, err = await ensure_disasm(False)
        reply({"t": "resp",
               "error": err} if err else {"t": "resp", "funcs": [
                   {"a": f"0x{f[0]:08x}", "n": f[2],
                    "sz": (f[1] or f[0]) - f[0]} for f in d["funcs"]]})
    elif t == "disasm":
        src = m.get("src") is True or str(m.get("src")) == "1"
        d, err = await ensure_disasm(src)
        if err:
            reply({"t": "resp", "error": err})
            return
        addr = int(m["addr"], 0) if m.get("addr") else None
        if addr is None and not m.get("func"):
            # 无 addr/func = 全量反汇编（执行剖析的指令标注覆盖所有热点）
            reply({"t": "resp", "func": None,
                   "rows": [list(r) for r in d["rows"]]})
            return
        f, rows = disasm_window(d, addr=addr, name=m.get("func"))
        reply({"t": "resp",
               "func": {"a": f"0x{f[0]:08x}", "n": f[2],
                        "sz": (f[1] or f[0]) - f[0]} if f else None,
               "rows": [list(r) for r in rows]})
    elif t == "sym":
        reply({"t": "resp", "elf": ST.elf_path,
               "count": len(ST.syms), "objects": len(ST.objs),
               "syms": [{"a": f"0x{a:08x}", "sz": s, "n": n, "t": "F"}
                        for a, s, n in ST.syms[:60]] +
                       [{"a": f"0x{a:08x}", "sz": s, "n": n, "t": "O"}
                        for a, s, n in ST.objs[:400]]})


async def ws_session(reader, writer, headers):
    if not await ws_handshake(writer, headers):
        writer.close()
        return
    sess = {"q": asyncio.Queue(maxsize=400), "tab": "console",
            "conport": 0, "con_q": None, "_writer": writer}
    ws_sub_con(sess, 0)
    tasks = [asyncio.create_task(t) for t in (
        ws_con_forwarder(sess), ws_pusher(sess))]

    async def sender():
        try:
            while True:
                obj = await sess["q"].get()
                try:
                    writer.write(ws_encode(
                        obj if isinstance(obj, str)
                        else json.dumps(obj, ensure_ascii=False)))
                    await writer.drain()
                except Exception as _e:
                    print(f"[send-err] {_e!r}", flush=True)
                    break
        except Exception:
            pass

    _send_task = asyncio.create_task(sender())
    tasks.append(_send_task)
    # 3 秒后检查 sender 是否还活着
    async def _check():
        await asyncio.sleep(3)
        print(f"[CHECK] sender done={_send_task.done()} cancelled={_send_task.cancelled()}", flush=True)
        if _send_task.done() and not _send_task.cancelled():
            print(f"[CHECK] sender exception={_send_task.exception()!r}", flush=True)
    tasks.append(asyncio.create_task(_check()))
    try:
        while True:
            raw = await ws_read_msg(reader, writer)
            if raw is None:
                break
            try:
                m = json.loads(raw)
            except ValueError:
                continue
            if isinstance(m, dict):
                try:
                    await ws_dispatch(sess, m)
                except Exception as e:
                    if isinstance(m, dict) and m.get("id") is not None:
                        try:
                            sess["q"].put_nowait(
                                {"t": "resp", "id": m["id"],
                                 "error": repr(e)})
                        except asyncio.QueueFull:
                            pass
    except (ConnectionError, asyncio.IncompleteReadError, OSError):
        pass
    finally:
        for tsk in tasks:
            tsk.cancel()
        if sess.get("con_q") is not None:
            ST.con_queues.discard(sess["con_q"])
            qs = ST.chan_queues.get(sess["conport"])
            if qs is not None:
                qs.discard(sess["con_q"])
        writer.close()


def active_chan_ports():
    """文本通道里累计 ≥16 字符的才算真通道——异常跟踪等流量下 resync
    会把 payload 字节误判成别端口 header，攒出一堆只收过几个字的假通道。"""
    return sorted([0] + [p for p, t in ST.chan_text.items() if len(t) >= 16])


def api_status():
    return {
        "uptime_s": round(time.time() - ST.t0, 1),
        "ocd": ST.ocd_ok,
        "swo": ST.swo_ok,
        "mhz": round(ST.mhz, 2),
        "gtc_hz": GTC_HZ,
        "pc_on": ST.pc_on, "exc_on": ST.exc_on,
        "pc_total": ST.pc_total, "pc_sleep": ST.pc_sleep,
        "exc_events": ST.exc_events,
        "resyncs": ST.resyncs, "overflows": ST.overflows,
        "tgt_state": ST.tgt_state, "halt_reason": ST.halt_reason,
        "halt_pc": f"0x{ST.halt_pc:08x}" if ST.halt_pc is not None else None,
        "backend": "jtag_tool", "swo_traceclk": ST.swo_traceclk,
        "swo_baud": ST.swo_baud,
        "swo_state": ST.swo_state,
        "swo_conn_n": ST.swo_conn_n,
        "swo_silent_s": round(time.time() - ST.swo_last_rx, 1)
        if ST.swo_last_rx else None,
        "swo_last_err": ST.swo_last_err,
        "chan_ports": active_chan_ports(),
        "event_port": ST.event_port,
        "evt_desync": ST.evt_desync, "evt_total": len(ST.events),
        "elf": ST.elf_path, "symbols": len(ST.syms),
        "objects": len(ST.objs),
    }


def api_events():
    """时间线：DWT 异常事件 + ITM 事件流按 GTC 归并。
    只保留最近 60s——固件侧事件停更（主循环卡死等）时，陈旧事件会把
    时间轴拉宽、活跃事件挤到右缘一条缝，看起来"没有刷新"。"""
    gs = [g for g, _, _ in ST.events] + [g for g, _, _ in ST.exc_recent]
    cutoff = (max(gs) - 60 * GTC_HZ) if gs else 0   # GTC 相对 60s 窗
    evs = [{"ms": round(g / (GTC_HZ / 1000), 3), "src": "evt",
            "type": t, "arg": a} for g, t, a in ST.events if g >= cutoff]
    evs += [{"ms": round(g / (GTC_HZ / 1000), 3), "src": "exc",
             "k": k, "exc": e} for g, k, e in ST.exc_recent if g >= cutoff]
    evs.sort(key=lambda x: x["ms"])
    return {"events": evs[-300:],
            "desync": ST.evt_desync, "stamp_drops": ST.stamp_drops}


def api_pcstats():
    now = time.time()
    elapsed = max(now - ST.pc_t0, 1e-3)
    top = sorted(ST.pc_hist.items(), key=lambda kv: -kv[1])[:25]
    total = ST.pc_total or 1
    return {
        "total": ST.pc_total, "sleep": ST.pc_sleep,
        "elapsed_s": round(elapsed, 1),
        "rate_per_s": round(ST.pc_total / elapsed, 1),
        "top": [{"pc": f"0x{a:08x}", "n": n, "pct": round(100.0 * n / total, 2),
                 "sym": ST.sym_lookup(a)} for a, n in top],
    }


def api_excstats():
    us = GTC_HZ / 1e6  # ticks -> us
    irqs = []
    for exc, d in sorted(ST.exc.items()):
        if not d["n"]:
            continue
        irqs.append({
            "exc": exc,
            "n": d["n"], "n_exit": d.get("n_exit", 0),
            "h_avg_us": round(d["h_sum"] / d["h_n"] / us, 3) if d["h_n"] else None,
            "h_max_us": round(d["h_max"] / us, 3),
            "t_avg_us": round(d["t_sum"] / d["t_n"] / us, 1) if d["t_n"] else None,
            "p_avg_us": round(d["p_sum"] / d["p_n"] / us, 1) if d["p_n"] else None,
        })
    return {
        "events": ST.exc_events, "resyncs": ST.resyncs,
        "mispaired": ST.exc_mispaired,
        "ret_avg_us": round(ST.r_sum / ST.r_n / us, 3) if ST.r_n else None,
        "irqs": irqs,
        "recent": [{"ms": round(g / (GTC_HZ / 1000), 3), "k": k, "exc": e}
                   for g, k, e in list(ST.exc_recent)[-30:]],
        "diag": {f"{k}|{e}": n for (k, e), n in sorted(ST.exc_diag.items())},
    }


async def sse_console(writer, port=0):
    q = asyncio.Queue(maxsize=2000)
    backbuf = ST.text if port == 0 else ST.chan_text.get(port)
    if port == 0:
        ST.con_queues.add(q)
    else:
        ST.chan_queues.setdefault(port, set()).add(q)
    writer.write(
        b"HTTP/1.0 200 OK\r\nContent-Type: text/event-stream\r\n"
        b"Cache-Control: no-cache\r\nConnection: close\r\n\r\n")
    try:
        back = "".join(backbuf)[-6000:] if backbuf else ""
        writer.write(b"data: " + json.dumps(
            {"s": back}, ensure_ascii=False).encode() + b"\n\n")
        await writer.drain()
        while True:
            try:
                chunk = await asyncio.wait_for(q.get(), 5.0)
                writer.write(b"data: " + json.dumps(
                    {"s": chunk}, ensure_ascii=False).encode() + b"\n\n")
            except asyncio.TimeoutError:
                writer.write(b": keep\n\n")
            await writer.drain()
    except Exception:
        pass
    finally:
        if port == 0:
            ST.con_queues.discard(q)
        else:
            qs = ST.chan_queues.get(port)
            if qs is not None:
                qs.discard(q)


async def handle_http(reader, writer):
    ws_hold = False
    try:
        method, path, headers, body = await read_req(reader)
        if method is None:
            return
        if (method == "GET" and path.split("?")[0] == "/ws"
                and "websocket" in headers.get("upgrade", "").lower()):
            ws_hold = True          # 连接由 ws_session 接管，finally 不许关
            await ws_session(reader, writer, headers)
            return
        p, _, query = path.partition("?")
        q = {}
        for kv in query.split("&"):
            if "=" in kv:
                k, v = kv.split("=", 1)
                q[k] = v
        if method == "GET":
            if p == "/":
                page = PAGE.encode("utf-8")
                writer.write(
                    "HTTP/1.0 200 OK\r\nContent-Type: text/html; "
                    f"charset=utf-8\r\nContent-Length: {len(page)}\r\n"
                    "Cache-Control: no-store\r\n"      # 不缓存：旧页面+新服务器=静默不兼容
                    "Connection: close\r\n\r\n".encode() + page)
            elif p == "/api/status":
                json_resp(writer, api_status())
            elif p == "/api/pcstats":
                if "clear" in path:
                    ST.pc_hist, ST.pc_total, ST.pc_t0 = {}, 0, time.time()
                json_resp(writer, api_pcstats())
            elif p == "/api/excstats":
                json_resp(writer, api_excstats())
            elif p == "/api/events":
                json_resp(writer, api_events())
            elif p == "/api/channels":
                json_resp(writer, {"ports": active_chan_ports(),
                                    "counts": {str(p): len(t) for p, t in
                                               ST.chan_text.items()},
                                    "event_port": ST.event_port})
            elif p == "/api/regs":
                json_resp(writer, {
                    "state": ST.tgt_state, "reason": ST.halt_reason,
                    "pc": (f"0x{ST.halt_pc:08x}"
                           if ST.halt_pc is not None else None),
                    "regs": {k: f"0x{v:08x}"
                             for k, v in ST.regs.items()}})
            elif p == "/api/mem":
                addr, size = resolve_sym(q.get("addr") or q.get("sym"))
                if addr is None:
                    json_resp(writer, {"error": "无法解析地址/符号"}, 400)
                    return
                w = {"4": 4, "2": 2, "1": 1}.get(q.get("w", "4"), 4)
                n = max(1, min(256, int(str(q.get("len", "64")), 0)))
                vals = await OCD.mem_read(addr, n, w)
                bs = b"".join(v.to_bytes(w, "little") for v in vals)
                json_resp(writer, {
                    "addr": f"0x{addr:08x}", "w": w, "vals":
                        [f"0x{v:0{2 * w}x}" for v in vals],
                    "ascii": "".join(chr(b) if 32 <= b < 127 else "."
                                     for b in bs)})
            elif p == "/api/bps":
                bps, wps = await refresh_bps()
                json_resp(writer, {
                    "bps": [{"addr": f"0x{b['addr']:08x}", "len": b["len"],
                             "hw": b["hw"]} for b in bps],
                    "wps": [{"addr": f"0x{w['addr']:08x}", "acc": w["acc"],
                             "len": w.get("len", 4)} for w in wps]})
            elif p == "/api/disasm/funcs":
                d, err = await ensure_disasm(False)
                if err:
                    json_resp(writer, {"error": err}, 400)
                    return
                json_resp(writer, {"funcs": [
                    {"a": f"0x{f[0]:08x}", "n": f[2], "sz": (f[1] or f[0]) - f[0]}
                    for f in d["funcs"]]})
            elif p == "/api/disasm":
                d, err = await ensure_disasm(q.get("src") == "1")
                if err:
                    json_resp(writer, {"error": err}, 400)
                    return
                addr = None
                if q.get("addr"):
                    addr = int(q["addr"], 0)
                f, rows = disasm_window(d, addr=addr, name=q.get("func"))
                json_resp(writer, {
                    "func": {"a": f"0x{f[0]:08x}", "n": f[2],
                             "sz": (f[1] or f[0]) - f[0]} if f else None,
                    "rows": [[*r] for r in rows]})
            elif p == "/api/watches":
                json_resp(writer, {"watches": [
                    {"name": w["name"], "addr": f"0x{w['addr']:08x}",
                     "size": w["size"], "fmt": w["fmt"],
                     "win": w.get("win", 1),
                     "series": [[round(t, 3), v] for t, v in w["series"]]}
                    for w in ST.watches]})
            elif p == "/api/dwt":
                json_resp(writer, {
                    "mhz": round(ST.mhz, 2), "exc_ps": round(ST.exc_ps, 1),
                    "sleep_pct": round(ST.sleep_pct, 1),
                    "raw": {"cyc": f"0x{ST.dwt_raw[0]:08x}",
                            "cpi": ST.dwt_raw[1], "exc": ST.dwt_raw[2],
                            "slp": ST.dwt_raw[3], "lsu": ST.dwt_raw[4],
                            "fold": ST.dwt_raw[5]},
                    "note": "cpi/exc/slp/lsu/fold 为 8 位计数器，忙循环下每"
                            "~35µs 回绕一次，轮询值仅定性参考"})
            elif p == "/api/symbols":
                json_resp(writer, {
                    "elf": ST.elf_path, "count": len(ST.syms),
                    "objects": len(ST.objs),
                    "syms": [{"a": f"0x{a:08x}", "sz": s, "n": n, "t": "F"}
                             for a, s, n in ST.syms[:60]] +
                            [{"a": f"0x{a:08x}", "sz": s, "n": n, "t": "O"}
                             for a, s, n in ST.objs[:400]]})
            elif p == "/api/console/stream":
                await sse_console(writer, int(q.get("port", 0)))
                return  # 连接已由 SSE 循环管理
            else:
                writer.write(b"HTTP/1.0 404 Not Found\r\n\r\n")
        elif method == "POST":
            if p == "/api/ctrl":
                v = await OCD.set_trace(
                    pc=body.get("pc"), exc=body.get("exc"))
                json_resp(writer, {"dwt_ctrl": f"0x{v:08x}",
                                   "warn": ("PC 采样+异常跟踪同开会饱和 4M SWO 线，"
                                            "printf/事件流会断流，建议分开开"
                                            ) if ST.pc_on and ST.exc_on else ""})
            elif p == "/api/target":
                act = body.get("action", "")
                if act in ("halt", "resume"):
                    out = await OCD.cmd(act)
                elif act == "reset":
                    # AIRCR SYSRESETREQ
                    await OCD.mww(0xE000ED0C, 0x05FA0004)
                    out = "reset (SYSRESETREQ)"
                elif act == "reset_halt":
                    await OCD.mww(0xE000ED0C, 0x05FA0004)
                    pc = await OCD.halt()
                    out = f"halted pc=0x{pc:08x}" if pc else "halt"
                else:
                    json_resp(writer, {"error": "bad action"}, 400)
                    return
                if act in ("halt", "reset_halt"):
                    await tgt_probe()
                json_resp(writer, {"action": act, "out": out.strip()[-800:]})
            elif p == "/api/step":
                n = max(1, min(16, int(body.get("n", 1) or 1)))
                pc = await OCD.step(n)
                await tgt_probe()
                await refresh_regs()
                json_resp(writer, {
                    "out": f"pc=0x{pc:08x}" if pc else "", "state": ST.tgt_state,
                    "reason": ST.halt_reason,
                    "regs": {k: f"0x{v:08x}"
                             for k, v in ST.regs.items()}})
            elif p == "/api/mem":
                addr, size = resolve_sym(body.get("addr"))
                if addr is None:
                    json_resp(writer, {"error": "无法解析地址/符号"}, 400)
                    return
                w = {"4": 4, "2": 2, "1": 1}.get(str(body.get("w", 4)), 4)
                try:
                    val = int(str(body.get("value", "")), 0)
                except ValueError:
                    json_resp(writer, {"error": "bad value"}, 400)
                    return
                out = await OCD.mem_write(addr, val, w)
                json_resp(writer, {"addr": f"0x{addr:08x}", "w": w,
                                   "out": out.strip()[-300:]})
            elif p == "/api/bp":
                # FPB/DWT 比较器经 AP 随时可写（免 halt）
                act = body.get("action", "")
                kind = body.get("kind", "bp")
                out = ""
                if act == "clr":
                    await OCD.bp_del()
                    await OCD.wp_del()
                    out = "cleared"
                else:
                    addr, _ = resolve_sym(body.get("addr"))
                    if addr is None:
                        json_resp(writer, {"error": "无法解析地址/符号"}, 400)
                        return
                    if kind == "bp":
                        if act == "add":
                            await OCD.bp_add(
                                addr, 4 if str(body.get("len", 2)) == "4"
                                else 2)
                            out = f"bp 0x{addr:08x}"
                        else:
                            await OCD.bp_del(addr)
                            out = "removed"
                    else:
                        if act == "add":
                            await OCD.wp_add(
                                addr, int(body.get("len", 4) or 4),
                                body.get("acc", "w"))
                            out = f"wp 0x{addr:08x}"
                        else:
                            await OCD.wp_del(addr)
                            out = "removed"
                await refresh_bps()
                json_resp(writer, {"out": out[-300:]})
            elif p == "/api/watch":
                act = body.get("action", "")
                name = str(body.get("name", "")).strip()
                fmt = str(body.get("fmt", "u32"))
                if act == "rate":
                    ST.watch_ms = max(50, min(5000,
                                               int(body.get("ms", 50) or 50)))
                    json_resp(writer, {"watch_ms": ST.watch_ms})
                    return
                if act == "setfmt":
                    ok, werr = watch_setfmt(name, fmt)
                    if not ok:
                        json_resp(writer, {"error": werr}, 400)
                        return
                    json_resp(writer, {"count": len(ST.watches)})
                    return
                if act == "add":
                    ok, werr = watch_add(name, fmt, body.get("win", 1))
                    if not ok:
                        json_resp(writer, {"error": werr}, 400)
                        return
                if act == "setwin":
                    ok, werr = watch_setwin(name, body.get("win", 1))
                    if not ok:
                        json_resp(writer, {"error": werr}, 400)
                        return
                    json_resp(writer, {"count": len(ST.watches)})
                    return
                elif act == "del":
                    ST.watches = [w for w in ST.watches if w["name"] != name]
                elif act == "clr":
                    ST.watches = []
                json_resp(writer, {"count": len(ST.watches)})
            elif p == "/api/eventport":
                ST.event_port = max(0, min(31, int(body.get("port", 2))))
                json_resp(writer, {"event_port": ST.event_port})
            elif p == "/api/swocfg":
                tc = int(body.get("traceclk", 72000000) or 72000000)
                tc = max(1_000_000, min(300_000_000, tc))
                ST.swo_traceclk = tc
                if body.get("baud"):
                    ST.swo_baud = int(body["baud"])
                actual = await OCD.swo_tpiu(tc, ST.swo_baud)
                json_resp(writer, {"traceclk": tc, "out": f"RX {actual} Hz"})
            elif p == "/api/cmd":
                out = await OCD.cmd(str(body.get("cmd", ""))[:200])
                json_resp(writer, {"out": out.strip()[-2000:]})
            else:
                writer.write(b"HTTP/1.0 404 Not Found\r\n\r\n")
    except Exception as e:
        try:
            json_resp(writer, {"error": repr(e)}, 500)
        except Exception:
            pass
    finally:
        if not ws_hold:            # ws_session 自己管理连接生命周期
            try:
                writer.close()
            except Exception:
                pass


# ---------------------------------------------------------------- 前端页面
PAGE = r"""
<!doctype html>
<html lang="zh-CN"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Trace Inspector · jtag_swd_dbg</title>
<style>
:root{
--bg:#0e1217;--pan:#161c24;--pan2:#1b232d;--pan3:#212b37;
--bd:#2a3644;--bd2:#38475a;--fg:#d9e2ec;--dim:#8494a5;--faint:#5b6b7c;
--acc:#4fc3f7;--acc2:#2196cd;--ok:#43c983;--warn:#e6b35a;--err:#e05d5d;
--vio:#9d8cff;--sel:#24344a;
--deep:#101720;--okbg:#12301f;--warnbg:#3a2c12;--errbg:#3a1414;
}
body.light{
--bg:#eef1f5;--pan:#ffffff;--pan2:#f3f6f9;--pan3:#e8edf2;
--bd:#d4dce4;--bd2:#b9c5d0;--fg:#1c2733;--dim:#57697c;--faint:#7d8ea0;
--acc:#0284c7;--acc2:#0369a1;--ok:#0f9d58;--warn:#b45309;--err:#dc2626;
--vio:#6d5ce0;--sel:#d7e9f7;
--deep:#e9eef3;--okbg:#e2f4ea;--warnbg:#f9eed3;--errbg:#fbe3e3;
}
*{box-sizing:border-box;margin:0;padding:0}
html,body{height:100%}
body{background:var(--bg);color:var(--fg);
font:13px/1.45 "SFMono-Regular","Cascadia Mono",Consolas,"Liberation Mono",monospace;
display:flex;flex-direction:column;overflow:hidden}
::-webkit-scrollbar{width:10px;height:10px}
::-webkit-scrollbar-thumb{background:var(--bd2);border-radius:5px}
::-webkit-scrollbar-track{background:transparent}

/* ---------- 顶部工具栏 ---------- */
#topbar{display:flex;align-items:center;gap:14px;padding:0 14px;height:46px;
background:linear-gradient(180deg,var(--pan2),var(--pan));border-bottom:1px solid var(--bd);
flex:none}
.brand{display:flex;align-items:baseline;gap:8px;font-size:14px;letter-spacing:.5px;
white-space:nowrap}
.brand b{color:var(--acc)}
.brand span{color:var(--dim);font-weight:400;font-size:12px}
.leds{display:flex;gap:12px;padding-left:14px;border-left:1px solid var(--bd);
font-size:12px;color:var(--dim);white-space:nowrap}
.led{display:inline-block;width:8px;height:8px;border-radius:50%;
background:var(--err);margin-right:5px;box-shadow:0 0 4px rgba(0,0,0,.5);vertical-align:0}
.led.on{background:var(--ok);box-shadow:0 0 6px rgba(67,201,131,.8)}
#topmetrics{display:flex;gap:16px;font-size:12px;color:var(--dim);white-space:nowrap;
overflow:hidden}
#topmetrics b{color:var(--fg);font-weight:400}
#spacer{flex:1}
.tbtn{background:var(--pan3);border:1px solid var(--bd2);color:var(--fg);
padding:5px 12px;font:inherit;font-size:12px;cursor:pointer;border-radius:4px;
white-space:nowrap}
.tbtn:hover{border-color:var(--acc);color:var(--acc)}
.tbtn.warn{color:var(--warn)}
.tbtn.warn:hover{border-color:var(--warn)}
.tbtn:active{transform:translateY(1px)}
.sw{display:inline-flex;align-items:center;gap:6px;font-size:12px;color:var(--dim);
cursor:pointer;user-select:none;white-space:nowrap}
.sw input{display:none}
.sw i{width:30px;height:16px;background:var(--pan3);border:1px solid var(--bd2);
border-radius:9px;position:relative;transition:.15s;font-style:normal}
.sw i::after{content:"";position:absolute;left:2px;top:2px;width:10px;height:10px;
border-radius:50%;background:var(--dim);transition:.15s}
.sw input:checked+i{background:var(--sel);border-color:var(--acc2)}
.sw input:checked+i::after{left:16px;background:var(--acc)}
.sw input:checked~span{color:var(--acc)}

/* ---------- 标签页 ---------- */
#tabs{display:flex;background:var(--pan);border-bottom:1px solid var(--bd);flex:none;
padding:0 8px}
#tabs button{background:none;border:none;color:var(--dim);padding:9px 16px 7px;
font:inherit;font-size:12.5px;cursor:pointer;border-bottom:2px solid transparent;
border-radius:3px 3px 0 0}
#tabs button:hover{color:var(--fg)}
#tabs button.on{color:var(--acc);border-bottom-color:var(--acc);background:var(--pan3)}

main{flex:1;overflow:hidden;padding:12px 14px}
section{display:none;height:100%;flex-direction:column;gap:10px}
#s-watch{overflow-y:auto}     /* 多窗画布往下排，超出屏才滚 */
section.on{display:flex}

/* ---------- 通用卡片/表 ---------- */
.cards{display:flex;gap:10px;flex-wrap:wrap;flex:none}
.card{background:var(--pan);border:1px solid var(--bd);border-radius:6px;
padding:8px 16px;min-width:118px}
.card .v{font-size:20px;font-weight:600;color:var(--fg)}
.card .v small{font-size:11px;color:var(--dim);font-weight:400}
.card .l{font-size:11px;color:var(--dim);margin-top:1px}
.card .v.ok{color:var(--ok)}.card .v.acc{color:var(--acc)}.card .v.warn{color:var(--warn)}
.card canvas{width:120px;height:26px;display:block;margin-top:4px}
.tblwrap{flex:1;overflow:auto;background:var(--pan);border:1px solid var(--bd);
border-radius:6px}
table{border-collapse:collapse;width:100%;font-size:12.5px}
th{position:sticky;top:0;background:var(--pan2);color:var(--dim);font-weight:400;
text-align:left;padding:7px 12px;border-bottom:1px solid var(--bd);white-space:nowrap;
z-index:1}
td{padding:6px 12px;border-bottom:1px solid #202a36;white-space:nowrap}
tr:hover td{background:var(--pan3)}
td.mono{color:var(--acc)}
.bar{position:relative;background:var(--deep);border-radius:3px;height:14px;min-width:150px;
overflow:hidden}
.bar i{position:absolute;inset:0 auto 0 0;border-radius:3px;
background:linear-gradient(90deg,var(--acc2),var(--acc))}
.bar span{position:relative;z-index:1;display:block;padding:0 6px;font-size:11px;
color:#eaf4fd;line-height:14px}
.empty{color:var(--faint);padding:26px;text-align:center}
.hint{color:var(--dim);font-size:11.5px}
.hint.warn{color:var(--warn)}
.cbtn{background:none;border:none;color:var(--dim);font:inherit;font-size:12px;
cursor:pointer;padding:1px 4px}
.cbtn:hover{color:var(--acc)}

/* ---------- 控制台 ---------- */
#conwrap{flex:1;display:flex;flex-direction:column;gap:0;background:var(--bg);
border:1px solid var(--bd);border-radius:6px;overflow:hidden}
#conhead{display:flex;align-items:center;gap:14px;padding:6px 12px;
background:var(--pan);border-bottom:1px solid var(--bd);flex:none;font-size:12px;
color:var(--dim)}
#conhead .cbtn{background:none;border:none;color:var(--dim);font:inherit;font-size:12px;
cursor:pointer;padding:1px 4px}
#conhead .cbtn:hover{color:var(--acc)}
#con{flex:1;overflow-y:auto;padding:10px 12px;white-space:pre-wrap;
word-break:break-all;font-size:12.5px;color:#bcd3e6}
#cmdline{display:flex;align-items:center;gap:8px;padding:7px 12px;
background:var(--pan);border-top:1px solid var(--bd);flex:none}
#cmdline .prompt{color:var(--acc);font-size:12.5px}
#cmd{flex:1;background:var(--bg);border:1px solid var(--bd);color:var(--fg);
font:inherit;font-size:12.5px;padding:5px 8px;border-radius:4px;outline:none}
#cmd:focus{border-color:var(--acc2)}
#cmdout{color:var(--faint);font-size:12px;max-width:40%;overflow:hidden;
text-overflow:ellipsis;white-space:nowrap}

/* ---------- 剖析分布条 ---------- */
#dist{display:flex;height:26px;border-radius:5px;overflow:hidden;flex:none;
border:1px solid var(--bd);background:var(--deep)}
#dist div{display:flex;align-items:center;justify-content:center;font-size:10.5px;
color:#0b1118;font-weight:600;overflow:hidden;white-space:nowrap;cursor:default}
#distleg{display:flex;gap:14px;flex-wrap:wrap;font-size:11px;color:var(--dim);
flex:none;min-height:16px}

/* ---------- 异常时间线 ---------- */
#tl{flex:none;background:var(--pan);border:1px solid var(--bd);border-radius:6px;
padding:10px 12px 6px;min-height:118px}
#tl .ttl{font-size:11px;color:var(--dim);margin-bottom:6px}
.lane{position:relative;height:22px;margin-bottom:2px}
.lane .lname{position:absolute;left:0;top:3px;font-size:10.5px;color:var(--dim);
z-index:2;background:var(--pan);padding-right:6px}
.lane .axis{position:absolute;inset:0 0 0 0;border-bottom:1px dashed #232e3b}
.ev{position:absolute;top:3px;width:4px;height:14px;border-radius:1px;cursor:default}
.ev.entry{background:var(--ok)}.ev.exit{background:var(--warn)}.ev.ret{background:var(--vio)}
.ev.evt{background:var(--acc);height:10px;top:5px}
#tlx{display:flex;justify-content:space-between;font-size:10px;color:var(--faint);
margin-top:3px}

/* ---------- 通道 pill ---------- */
#chpills{display:flex;gap:4px;flex-wrap:wrap}
.pill{background:var(--pan3);border:1px solid var(--bd2);color:var(--dim);
font:inherit;font-size:11px;padding:1px 8px;border-radius:9px;cursor:pointer}
.pill:hover{border-color:var(--acc);color:var(--acc)}
.pill.on{background:var(--sel);border-color:var(--acc2);color:var(--acc)}
.pill .ep{color:var(--vio);font-size:10px}

/* ---------- 目标状态徽标 ---------- */
#t_state{font-size:12px;white-space:nowrap}
#t_state .b{display:inline-block;padding:1px 9px;border-radius:9px;font-size:11px}
#t_state .run{background:var(--okbg);color:var(--ok);border:1px solid #1e5c3a}
#t_state .hlt{background:var(--warnbg);color:var(--warn);border:1px solid #6b5220}
#t_state .unk{background:var(--pan3);color:var(--dim);border:1px solid var(--bd2)}

/* ---------- 寄存器网格 ---------- */
.reggrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));
gap:4px 10px;align-content:start}
.rg{display:flex;justify-content:space-between;gap:8px;background:var(--pan2);
border:1px solid #222d3a;border-radius:4px;padding:3px 8px;font-size:12px}
.rg .n{color:var(--dim)}
.rg .v{color:var(--acc)}
.rg.chg{border-color:#3d5a2e}.rg.chg .v{color:var(--ok)}
.regwide{grid-column:1/-1;display:flex;gap:10px;flex-wrap:wrap;align-items:center;
background:var(--pan2);border:1px solid #222d3a;border-radius:4px;
padding:4px 8px;font-size:12px}
.flag{display:inline-block;min-width:16px;text-align:center;padding:0 3px;
border-radius:3px;background:var(--bg);color:var(--faint);border:1px solid var(--bd)}
.flag.on{color:var(--warn);border-color:#6b5220;background:var(--warnbg)}

/* ---------- 内存浏览器 ---------- */
#memtbl{font-size:12px;border-collapse:collapse;width:100%}
#memtbl td,#memtbl th{padding:2px 8px;border-bottom:1px solid #1b242f;
white-space:nowrap;text-align:left}
#memtbl th{color:var(--dim);font-weight:400;position:sticky;top:0;
background:var(--pan2)}
#memtbl td.a{color:var(--faint)}
#memtbl td.c{cursor:pointer}
#memtbl td.c:hover{background:var(--sel);color:var(--acc)}
#memasc{color:var(--faint)}

/* ---------- 反汇编分栏 ---------- */
#diswrap{flex:1;display:flex;gap:10px;overflow:hidden}
#dfuncs{width:240px;flex:none;overflow:auto;background:var(--pan);
border:1px solid var(--bd);border-radius:6px}
#dfuncs div{padding:4px 10px;font-size:12px;color:var(--dim);cursor:pointer;
border-bottom:1px solid #1b242f;white-space:nowrap;overflow:hidden;
text-overflow:ellipsis}
#dfuncs div:hover{color:var(--acc);background:var(--pan3)}
#dfuncs div.on{color:var(--acc);background:var(--sel)}
#dcode{flex:1;overflow:auto;background:var(--pan);border:1px solid var(--bd);
border-radius:6px}
#dcode pre{font-size:12px;line-height:1.5;padding:8px 0}
.drow{padding:0 14px;white-space:pre}
.dgp{display:inline-block;width:22px;min-height:14px;color:var(--faint);
cursor:pointer;text-align:center;font-weight:700;user-select:none}
.dgp:hover{background:var(--pan3);border-radius:3px}
.dgp.on{color:#e05d5d}
.drow .da{color:var(--faint);display:inline-block;min-width:78px}
.drow .db{color:var(--vio);display:inline-block;min-width:78px}
.drow.src{color:#7fa87f;opacity:.85;white-space:pre-wrap}
.drow.fn{color:var(--acc);background:var(--pan3);margin-top:6px}
.drow.pchit{background:var(--warnbg);outline:1px solid #6b5220}
.drow:hover:not(.src){background:var(--pan3)}

/* ---------- 调试工具栏（IDE 式连体组） ---------- */
#dbgbar{display:flex;align-items:center;gap:6px;padding:6px 10px;flex:none;
background:var(--pan);border:1px solid var(--bd);border-radius:6px}
#dbgbar .db{background:var(--pan2);border:1px solid var(--bd);color:var(--fg);
font:inherit;font-size:12px;padding:5px 12px;cursor:pointer;white-space:nowrap}
#dbgbar .db:hover{background:var(--pan3);color:var(--acc)}
#dbgbar .db.primary{color:var(--ok);border-color:var(--ok);font-weight:600}
#dbgbar .db.warn{color:var(--warn)}
#dbgbar .dsep{width:1px;height:20px;background:var(--bd);margin:0 4px}
/* ---------- 变量 watch ---------- */
#wchart{width:100%;background:var(--pan);border:1px solid var(--bd);
border-radius:6px;flex:none}
#wleg{display:flex;gap:14px;flex-wrap:wrap;font-size:11.5px;color:var(--dim);
flex:none}
#wtabs{display:flex;gap:4px}
#wtabs button{background:transparent;border:1px solid var(--bd);color:var(--dim);
font:inherit;font-size:11.5px;padding:4px 10px;border-radius:4px;cursor:pointer}
#wtabs button.on{color:var(--acc);border-color:var(--acc)}
.whov{position:absolute;background:var(--deep);border:1px solid var(--bd2);
border-radius:4px;padding:4px 8px;font-size:11px;pointer-events:none;
display:none;z-index:5;line-height:1.5}
input[type=text].sm{width:170px}
select{background:var(--bg);border:1px solid var(--bd);color:var(--fg);
font:inherit;font-size:12px;padding:5px 6px;border-radius:4px;outline:none}

/* ---------- 目标页 ---------- */
.row{display:flex;gap:10px;align-items:center;flex-wrap:wrap;flex:none}
input[type=text]{background:var(--bg);border:1px solid var(--bd);color:var(--fg);
font:inherit;font-size:12.5px;padding:6px 9px;border-radius:4px;outline:none;
width:340px}
input[type=text]:focus{border-color:var(--acc2)}
.box{background:var(--pan);border:1px solid var(--bd);border-radius:6px;
padding:10px 14px;flex:none}
.box h3{font-size:11.5px;color:var(--dim);font-weight:400;margin-bottom:8px;
letter-spacing:.5px}

/* ---------- 底部状态栏 ---------- */
#statusbar{display:flex;align-items:center;gap:16px;padding:0 14px;height:26px;
background:var(--pan);border-top:1px solid var(--bd);font-size:11.5px;
color:var(--dim);flex:none;white-space:nowrap;overflow:hidden}
#statusbar .r{margin-left:auto}
#sb_up{color:var(--fg)}
</style></head><body>

<div id="topbar">
 <div class="brand"><b>jtag_swd_dbg</b>TRACE<b>INSPECTOR</b><span>Cortex-M3 SWO</span></div>
 <div class="leds">
  <span><i class="led" id="d_ocd"></i>jtag_tool</span>
  <span><i class="led" id="d_swo"></i>SWO</span>
 </div>
 <div id="t_state"><span class="b unk">—</span></div>
 <div id="topmetrics">
  <span>CPU <b id="t_mhz">—</b></span>
  <span>样本 <b id="t_pc">0</b></span>
  <span>事件 <b id="t_exc">0</b></span>
  <span>resync <b id="t_rs">0</b></span>
 </div>
 <div id="spacer"></div>
 <label class="sw"><input type="checkbox" id="t_pc_on" onchange="ctrl(this.checked,null)"><i></i><span>PC 采样</span></label>
 <label class="sw"><input type="checkbox" id="t_exc_on" onchange="ctrl(null,this.checked)"><i></i><span>异常跟踪</span></label>
 <button class="tbtn" id="themeBtn" onclick="themeToggle()" title="亮/暗主题">☀</button>
</div>

<div id="tabs">
 <button data-t="console" class="on">控制台</button>
 <button data-t="prof">执行剖析</button>
 <button data-t="exc">异常分析</button>
 <button data-t="tl2">时间线</button>
 <button data-t="dwt">性能计数</button>
 <button data-t="debug">调试</button>
 <button data-t="watch">变量</button>
 <button data-t="target">目标</button>
</div>

<main>
<!-- ============ 控制台 ============ -->
<section id="s-console" class="on">
 <div id="conwrap">
  <div id="conhead">
   <span id="conlabel">ITM 通道</span>
   <div id="chpills"></div>
   <div style="flex:1"></div>
   <label class="sw" style="font-size:11.5px"><input type="checkbox" id="autoscroll" checked><i></i><span>自动滚动</span></label>
   <button class="cbtn" onclick="conClear()">清屏</button>
   <button class="cbtn" onclick="conSave()">保存…</button>
  </div>
  <pre id="con"></pre>
  <div id="cmdline">
   <span class="prompt">jtag_tool &gt;</span>
   <input type="text" id="cmd" placeholder="mdw 0xE0001004 / reg pc / step 4 …（回车执行）" onkeydown="if(event.key=='Enter')rawCmd()">
   <span id="cmdout"></span>
  </div>
 </div>
</section>

<!-- ============ 执行剖析 ============ -->
<section id="s-prof">
 <div class="cards">
  <div class="card"><div class="v" id="p_total">0</div><div class="l">PC 样本总数</div></div>
  <div class="card"><div class="v acc" id="p_rate">—</div><div class="l">采样率 /s</div></div>
  <div class="card"><div class="v" id="p_elapsed">—</div><div class="l">累计时长</div></div>
  <div class="card"><div class="v" id="p_sleep">0</div><div class="l">sleep 样本</div></div>
  <div class="card" style="flex:1;min-width:220px;display:flex;align-items:center">
   <span class="hint" id="p_hint">未开启——工具栏打开「PC 采样」</span>
  </div>
 </div>
 <div id="dist"><div style="flex:1;background:var(--deep)"></div></div>
 <div id="distleg"></div>
 <div class="tblwrap"><table id="p_tbl">
  <thead><tr><th>热度</th><th>符号 + 偏移</th><th>地址</th><th>样本</th><th>占比</th></tr></thead>
  <tbody></tbody></table></div>
 <div class="hint warn">· DWT PCSAMPLENA，r1p1 周期固定 ~1024 拍（72M→~70K/s）；与异常跟踪同开会饱和 4M SWO 线 → 目标侧丢包，建议分开开</div>
</section>

<!-- ============ 异常分析 ============ -->
<section id="s-exc">
 <div class="cards">
  <div class="card"><div class="v" id="e_events">0</div><div class="l">事件总数</div></div>
  <div class="card"><div class="v acc" id="e_ret">—</div><div class="l">exit→ret 路径 µs</div></div>
  <div class="card"><div class="v" id="e_mis">0</div><div class="l">误配剔除</div></div>
  <div class="card"><div class="v" id="e_rs">0</div><div class="l">流 resync</div></div>
  <div class="card" style="flex:1;min-width:220px;display:flex;align-items:center">
   <span class="hint" id="e_hint">未开启——工具栏打开「异常跟踪」</span>
  </div>
 </div>
 <div id="tl">
  <div class="ttl">最近事件时间线（GTC）· <span style="color:var(--ok)">■</span> entry&nbsp;<span style="color:var(--warn)">■</span> exit&nbsp;<span style="color:var(--vio)">■</span> ret</div>
  <div id="tl_lanes"><div class="empty" style="padding:10px">暂无事件</div></div>
  <div id="tlx"><span id="tlx0"></span><span id="tlx1"></span></div>
 </div>
 <div class="tblwrap"><table id="e_tbl" style="table-layout:fixed">
  <colgroup><col style="width:140px"><col style="width:36px"><col style="width:15%"><col style="width:60px">
   <col style="width:18%"><col style="width:16%"><col style="width:12%"></colgroup>
  <thead><tr><th>频次</th><th>#</th><th>异常</th><th>次数</th>
   <th>handler µs (entry→exit)</th><th>触发延迟 µs (ret→entry)</th><th>周期 µs</th></tr></thead>
  <tbody></tbody></table></div>
</section>

<!-- ============ 性能计数 ============ -->
<section id="s-dwt">
 <div class="cards">
  <div class="card"><div class="v ok" id="g_mhz">—</div><div class="l">核心频率 MHz</div><canvas id="c_mhz"></canvas></div>
  <div class="card"><div class="v acc" id="g_exc">—</div><div class="l">异常事件 /s</div><canvas id="c_exc"></canvas></div>
  <div class="card"><div class="v warn" id="g_slp">—</div><div class="l">睡眠 %</div><canvas id="c_slp"></canvas></div>
  <div class="card"><div class="v" id="g_ovf">—</div><div class="l">SWO overflow</div></div>
 </div>
 <div class="tblwrap"><table id="d_tbl">
  <thead><tr><th>计数器</th><th>原始值</th><th>说明</th></tr></thead>
  <tbody>
   <tr><td>CYCCNT</td><td id="r_cyc" class="mono"></td><td>周期计数（32 位）</td></tr>
   <tr><td>CPICNT</td><td id="r_cpi" class="mono"></td><td>额外周期（8 位）</td></tr>
   <tr><td>EXCCNT</td><td id="r_exc" class="mono"></td><td>异常开销周期（8 位）</td></tr>
   <tr><td>SLEEPCNT</td><td id="r_slp" class="mono"></td><td>睡眠周期（8 位）</td></tr>
   <tr><td>LSUCNT</td><td id="r_lsu" class="mono"></td><td>访存额外周期（8 位）</td></tr>
   <tr><td>FOLDCNT</td><td id="r_fold" class="mono"></td><td>折叠周期（8 位）</td></tr>
  </tbody></table></div>
 <div class="hint">· 250ms mdw 轮询；GTC 时基 = 72MHz = HCLK；cpi/exc/slp/lsu/fold 为 8 位计数器，忙循环下 ~35µs 回绕一次，仅定性参考</div>
</section>

<!-- ============ 时间线 ============ -->
<section id="s-tl2">
 <div class="cards">
  <div class="card"><div class="v acc" id="w_ev">0</div><div class="l">事件总数(窗口)</div></div>
  <div class="card"><div class="v" id="w_des">0</div><div class="l">事件 desync</div></div>
  <div class="card"><div class="v" id="w_sdr">0</div><div class="l">stamp 丢弃</div></div>
  <div class="card" style="flex:1;min-width:260px;display:flex;align-items:center">
   <span class="hint">DWT 异常事件 + ITM 事件流（port <b id="w_evp">2</b>，1B type + 4B arg）按 GTC 归并。事件端口
     <input type="text" class="sm" id="evport" style="width:44px" value="2">
     <button class="tbtn" onclick="setEvPort()">设定</button>
     （固件侧 ITM TER 需使能对应位）</span>
  </div>
 </div>
 <div id="tl2box" style="flex:1;overflow:auto;background:var(--pan);
  border:1px solid var(--bd);border-radius:6px;padding:10px 12px 6px">
  <div class="ttl" style="font-size:11px;color:var(--dim);margin-bottom:6px">事件时间线（最近 300 条，按源分 lane）·
   <span style="color:var(--ok)">■</span> entry&nbsp;<span style="color:var(--warn)">■</span> exit&nbsp;<span style="color:var(--vio)">■</span> ret&nbsp;<span style="color:var(--acc)">■</span> ITM 事件</div>
  <div id="tl2_lanes"><div class="empty" style="padding:10px">暂无事件（异常跟踪 / 事件流固件未开）</div></div>
  <div id="tl2x" style="display:flex;justify-content:space-between;font-size:10px;color:var(--faint);margin-top:3px"><span></span><span></span></div>
 </div>
</section>

<!-- ============ 调试 ============ -->
<section id="s-debug">
 <div id="dbgbar">
  <button class="db primary" id="dbgRun" onclick="tgtToggle()" title="Halt/运行（随状态切换）">⏸ Halt</button>
  <span class="dsep"></span>
  <button class="db" onclick="stepN(1)" title="单步一条指令">⤵ 单步</button>
  <button class="db" onclick="stepN(4)" title="连走四条">×4</button>
  <span class="dsep"></span>
  <button class="db warn" onclick="target('reset_halt')" title="复位并停在入口">⟲ 复位·停</button>
  <button class="db warn" onclick="target('reset')" title="复位并运行">⟳ 复位·跑</button>
  <span class="dsep"></span>
  <button class="db" onclick="jumpPcDis()" title="反汇编定位到当前 PC">⇢ 定位 PC</button>
  <span class="hint" id="dbgbarInfo" style="margin-left:auto"></span>
 </div>
 <div class="row" style="align-items:stretch;flex:1;min-height:0;flex-wrap:nowrap;overflow:hidden">
  <div class="box" style="flex:0.95;min-width:270px;overflow:auto">
   <h3 id="dbgh">核心寄存器 · <span id="dbgreason">—</span></h3>
   <div class="reggrid" id="reggrid"><span class="hint">—</span></div>
  </div>
  <div style="flex:1.9;display:flex;flex-direction:column;gap:10px;min-width:460px;min-height:0;overflow:hidden">
   <div class="row" style="flex:none">
    <input type="text" id="disjump" placeholder="反汇编跳转：符号或地址（回车）" style="width:250px"
      onkeydown="if(event.key=='Enter')disJump($('disjump').value)">
    <label class="sw" style="font-size:11.5px"><input type="checkbox" id="dissrc" onchange="disReload()"><i></i><span>源码交错</span></label>
    <span class="hint" id="disinfo"></span>
   </div>
   <div id="diswrap">
    <div id="dfuncs"><div class="empty" style="padding:10px">加载 ELF 后出函数列表</div></div>
    <div id="dcode"><pre id="dpre"></pre></div>
   </div>
  </div>
  <div style="flex:1.35;display:flex;flex-direction:column;gap:10px;min-width:380px;min-height:0;overflow:hidden">
   <div class="box">
    <h3>内存浏览器</h3>
    <div class="row">
     <input type="text" id="memaddr" list="wl_syms" placeholder="地址或符号：0x20000000 / g_ticks" style="width:220px">
     <select id="memw"><option value="4">字</option><option value="2">半字</option><option value="1">字节</option></select>
     <input type="text" class="sm" id="memlen" value="64" style="width:52px" title="单元数">
     <button class="tbtn" onclick="memGo()">读取</button>
     <button class="tbtn" onclick="memWatch()">＋监控</button>
     <span class="hint" id="meminfo"></span>
    </div>
   </div>
   <div class="tblwrap" style="min-height:120px;flex:1"><table id="memtbl">
    <thead><tr><th>地址</th><th colspan="8" id="memh">值（点击编辑）</th></tr></thead>
    <tbody></tbody></table></div>
   <div class="box">
    <h3>断点 / 观察点</h3>
    <div class="row">
     <input type="text" id="bpaddr" placeholder="地址或符号" style="width:210px">
     <input type="text" class="sm" id="bplen" value="2" style="width:44px" title="长度">
     <select id="bpkind">
      <option value="bp">断点 hw 半字</option>
      <option value="bp4">断点 hw 4字节</option>
      <option value="wpr">观察点 读</option>
      <option value="wpw">观察点 写</option>
      <option value="wpa">观察点 读写</option>
     </select>
     <button class="tbtn" onclick="bpAdd()">添加</button>
     <button class="tbtn warn" onclick="bpClr()">全部清除</button>
     <span class="hint" id="bpout" style="max-width:30%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap"></span>
    </div>
   </div>
   <div class="tblwrap" style="max-height:150px"><table id="bp_tbl">
    <thead><tr><th>类型</th><th>地址</th><th>长度</th><th>值过滤</th><th></th></tr></thead>
    <tbody></tbody></table></div>
  </div>
 </div>
</section>

<!-- ============ 变量 ============ -->
<section id="s-watch">
 <div class="row" style="flex:none">
  <input type="text" id="wname" list="wl_syms" placeholder="全局变量名（ELF STT_OBJECT）或 0x 地址：g_ticks" style="width:270px"
    onkeydown="if(event.key=='Enter')watchAdd()">
  <datalist id="wl_syms"></datalist>
  <select id="wfmt"><option value="u32">u32</option><option value="i32">i32</option>
   <option value="hex">hex</option><option value="u16">u16</option>
   <option value="i16">i16</option><option value="u8">u8</option>
   <option value="i8">i8</option><option value="f32">f32</option>
   <option value="u64">u64</option><option value="i64">i64</option>
   <option value="f64">f64</option></select>
  <button class="tbtn" onclick="watchAdd()">添加</button>
  <button class="tbtn warn" onclick="watchClr()">清空</button>
  <span class="hint" id="winfo"></span>
  <span style="flex:1"></span>
  <span class="hint">采样</span>
  <input type="text" class="sm" id="wrate" value="50" style="width:52px" title="采样周期 ms"
    onkeydown="if(event.key=='Enter')watchRate()">
  <span class="hint">ms ⏎</span>
 </div>
 <div class="row" style="flex:none;gap:6px">
  <div id="wtabs">
   <button data-m="line" class="on" onclick="wMode('line')">曲线</button>
   <button data-m="gauge" onclick="wMode('gauge')">仪表盘</button>
   <button data-m="bits" onclick="wMode('bits')">位视图</button>
   <button data-m="hist" onclick="wMode('hist')">直方图</button>
  </div>
  <span style="flex:1"></span>
  <span class="hint">时基</span>
  <select id="wtb" onchange="wTbSave(this.value);drawW()">
   <option value="2">2 s</option><option value="5">5 s</option>
   <option value="10" selected>10 s</option><option value="30">30 s</option>
   <option value="60">60 s</option><option value="0">全部</option>
  </select>
  <label class="sw" style="font-size:11.5px"><input type="checkbox" id="wpause" onchange="wPause(this.checked)"><i></i><span>暂停显示</span></label>
  <select id="wtrigvar" title="触发变量"></select>
  <select id="wtrigcmp"><option value="&gt;">&gt;</option><option value="&lt;">&lt;</option></select>
  <input type="text" class="sm" id="wtrigv" placeholder="阈值" style="width:64px">
  <button class="tbtn" id="wtrigbtn" onclick="wTrigToggle()">触发：关</button>
 </div>
 <div style="position:relative;flex:none">
  <canvas id="wchart" style="display:block"></canvas>
  <div class="whov" id="whov"></div>
 </div>
 <div id="wleg"></div>
 <div class="tblwrap"><table id="w_tbl" style="table-layout:fixed">
  <colgroup>
   <col style="width:24px"><col style="width:20%"><col style="width:90px">
   <col style="width:64px"><col style="width:60px"><col style="width:110px">
   <col style="width:72px"><col style="width:72px"><col style="width:52px">
   <col style="width:36px">
  </colgroup>
  <thead><tr><th></th><th>变量</th><th>地址</th><th>格式</th><th>窗口</th><th>当前值</th><th>min</th><th>max</th><th>采样点</th><th></th></tr></thead>
  <tbody></tbody></table></div>
 <div class="hint">· mdw 轮询（运行/停止都采，停止时值冻结为平线）；u16/u8 为子字提取，f32 按 IEEE754 重解释；watch 列表存 localStorage，换 ELF 自动按名字重解析；
   触发=阈值单次：命中后画面冻结在触发瞬间，重新武装继续</div>
</section>

<!-- ============ 目标 ============ -->
<section id="s-target">
 <div class="box"><h3>符号表 · ELF .symtab（纯 python 解析，STT_FUNC）</h3>
  <div class="row">
   <span class="hint">ELF 由 swo_web.py 启动参数指定（当前：<span class="mono" id="elf_path_show">—</span>）</span>
   <span class="hint" id="elf_info"></span>
  </div></div>
 <div class="box"><h3>DWT 跟踪开关</h3>
  <div class="row">
   <label class="sw"><input type="checkbox" id="t_pc2" onchange="ctrl(this.checked,null)"><i></i><span>PC 采样（PCSAMPLENA）</span></label>
   <label class="sw"><input type="checkbox" id="t_exc2" onchange="ctrl(null,this.checked)"><i></i><span>异常跟踪（EXCTRCENA）</span></label>
  </div></div>
 <div class="box"><h3>SWO 接收配置（连接时自动代配；目标时钟变了在此重配）</h3>
  <div class="row">
   traceclk <input type="text" class="sm" id="swotc" value="72000000" style="width:90px"> Hz
   波特率 <select id="swobaud">
    <option value="1000000">1M</option>
    <option value="4000000">4M</option>
    <option value="8000000" selected>8M</option>
    <option value="12000000">12M</option>
   </select>
   <button class="tbtn" onclick="swoCfg()">重配</button>
   <span class="hint">= 目标 HCLK/TRACECLK（72M PLL 或复位初期 8M HSI）；引脚波特率固定 4M 档</span>
  </div></div>
 <div class="tblwrap"><table id="sy_tbl">
  <thead><tr><th>地址</th><th>大小</th><th>符号（变量可＋监控）</th></tr></thead>
  <tbody></tbody></table></div>
</section>
</main>

<div id="statusbar">
 <span><i class="led" id="sb_ocd"></i>jtag_tool</span>
 <span><i class="led" id="sb_swo"></i>SWO 流</span>
 <span>GTC 72 MHz</span>
 <span id="sb_up">00:00</span>
 <span class="r" id="sb_right"></span>
</div>

<script>
"use strict";
function cvc(d,l){return document.body.classList.contains("light")?l:d;}
const $=id=>document.getElementById(id);
const UI_VER="v56";   // 页面代次：状态栏右下可见；对不上=浏览器缓存了旧页
const esc=s=>String(s).replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));
const EXCN={2:"NMI",3:"HardFault",4:"MemManage",5:"BusFault",6:"UsageFault",
11:"SVCall",12:"DebugMon",14:"PendSV",15:"SysTick"};
const excName=n=>EXCN[n]||(n>=16?"IRQ"+(n-16):"#"+n);
const fmtUp=s=>{s|=0;const h=s/3600|0,m=(s%3600)/60|0,x=s%60;
return h?`${h}:${String(m).padStart(2,"0")}:${String(x).padStart(2,"0")}`
:`${String(m).padStart(2,"0")}:${String(x).padStart(2,"0")}`};
let tab="console";
const DCOLORS=["#0072BD","#D95319","#EDB120","#7E2F8E","#77AC30","#4DBEEE","#A2142F","#4fc3f7"];/* MATLAB 色序 */

/* ---- tabs ---- */
function showTab(t){tab=t;wsSend({t:"tab",v:t});
  localStorage.setItem("swo_tab",t);   // 刷新回到当前 tab
  history.replaceState(null,"","#"+t); // 同步 URL hash（不产生历史记录）——
                                       // 否则 hash 停在首次打开的 #watch，
                                       // 刷新恢复优先读 hash = 总跳回旧 tab
  document.querySelectorAll("#tabs button").forEach(x=>x.classList.toggle("on",x.dataset.t===t));
  document.querySelectorAll("main section").forEach(s=>s.classList.toggle("on",s.id=="s-"+t));
  if(tab=="dwt")sizeSparks();}
for(const b of document.querySelectorAll("#tabs button"))
  b.onclick=()=>showTab(b.dataset.t);
/* 注意：不能在此直接 showTab(location.hash)——wsSend 会引用尚未执行到的
 * let ws（TDZ），带 #tab 打开页面时整个脚本当场崩死（曾致"页面无响应"）。
 * 哈希初始化挪到脚本末尾 ws 声明之后 */

/* ---- WebSocket 实时通道 ---- */
const con=$("con");
let ws=null,wsId=1;const wsPend={};
function wsConnect(){
  ws=new WebSocket(`ws://${location.host}/ws`);
  ws.onopen=()=>{wsSend({t:"tab",v:tab});openCon(curCh);};
  ws.onmessage=e=>{const m=JSON.parse(e.data);
    if(m.id&&wsPend[m.id]){wsPend[m.id](m);delete wsPend[m.id];return;}
    if(m.t==="push")handlePush(m);
    else if(m.t==="con"){con.textContent+=m.s;
      if($("autoscroll").checked)con.scrollTop=con.scrollHeight;}};
  ws.onclose=()=>{setTimeout(wsConnect,1000);};}
function wsSend(o){if(ws&&ws.readyState===1)ws.send(JSON.stringify(o));}
function wreq(o){return new Promise(res=>{o.id=++wsId;wsPend[o.id]=res;wsSend(o);});}
let curCh=0;
function openCon(ch){curCh=ch;
  wsSend({t:"conport",v:ch});
  con.textContent="…";
  wreq({t:"conback",v:ch}).then(m=>{con.textContent=m.s||"";
    if($("autoscroll").checked)con.scrollTop=con.scrollHeight;});
  renderPills();}
function renderPills(){
  const ports=window._chports||[0],ep=window._evport??2;
  $("chpills").innerHTML=ports.map(p=>
    `<span class="pill${p===curCh?" on":""}" onclick="openCon(${p})">ch${p}${p===ep?'<span class="ep"> ⚑evt</span>':''}</span>`).join("");}
async function setEvPort(){
  const p=parseInt($("evport").value,10);
  const r=await post("/api/eventport",{port:p});
  window._evport=r.event_port;renderPills();$("w_evp").textContent=r.event_port;}
function conClear(){con.textContent="";}
function conSave(){const a=document.createElement("a");
  a.href=URL.createObjectURL(new Blob([con.textContent],{type:"text/plain"}));
  a.download="swo-console.txt";a.click();}
async function post(u,o){
  const m={...o};
  if(u==="/api/ctrl"){m.t="ctrl";}
  else if(u==="/api/target"){m.t="action";m.a=o.action;}
  else if(u==="/api/cmd"){m.t="cmd";m.line=o.cmd;}
  else if(u==="/api/step"){m.t="step";}
  else if(u==="/api/mem"){m.t="memw";}
  else if(u==="/api/bp"){m.t="bp";}
  else if(u==="/api/watch"){m.t="watch";}
  else if(u==="/api/eventport"){m.t="eventport";}
  else if(u==="/api/swocfg"){m.t="swocfg";}
  else{return {error:"no route "+u};}
  return wreq(m);}
async function ctrl(pc,exc){const r=await post("/api/ctrl",{pc,exc});
  $("cmdout").textContent=r.error||(`DWT_CTRL = ${r.dwt_ctrl}`+(r.warn?` ⚠ ${r.warn}`:""));}
async function target(a){const r=await post("/api/target",{action:a});
  $("cmdout").textContent=r.error||(r.out||"(no output)");
  con.textContent+=`\n[jtag_tool] ${a}: ${r.out||r.error||""}\n`;
  if($("autoscroll").checked)con.scrollTop=con.scrollHeight;}
async function rawCmd(){const c=$("cmd").value;if(!c)return;$("cmd").value="";
  $("cmdout").textContent="…";
  const r=await post("/api/cmd",{cmd:c});
  $("cmdout").textContent="";
  con.textContent+=`\n[jtag_tool] > ${c}\n${r.out||r.error||""}\n`;
  if($("autoscroll").checked)con.scrollTop=con.scrollHeight;}
async function swoCfg(){
  const r=await post("/api/swocfg",{traceclk:parseInt($("swotc").value)||72000000,
    baud:parseInt($("swobaud").value)||8000000});
  $("elf_info").textContent=r.error||`SWO 重配: ${r.out||""}`;}

/* ---- 走势图 ---- */
const H={mhz:[],exc:[],slp:[]};
function sizeSparks(){for(const id of["c_mhz","c_exc","c_slp"]){
  const cv=$(id);cv.width=cv.clientWidth*2||240;cv.height=52;}}
function spark(id,arr,color){const cv=$(id);if(!cv.width)sizeSparks();
  const x=cv.getContext("2d");x.clearRect(0,0,cv.width,cv.height);
  if(arr.length<2)return;
  const mn=Math.min(...arr),mx=Math.max(...arr),lo=mn===mx?mn-1:mn,hi=mn===mx?mn+1:mx;
  x.beginPath();
  arr.forEach((v,i)=>{const px=i/(arr.length-1)*cv.width,
    py=cv.height-(v-lo)/(hi-lo)*(cv.height-6)-3;i?x.lineTo(px,py):x.moveTo(px,py);});
  x.strokeStyle=color;x.lineWidth=2.5;x.stroke();}
function push(arr,v){arr.push(v);if(arr.length>90)arr.shift();}

/* ---- WS 推送驱动 ---- */
function handlePush(m){
 try{
  const s=m.status;
  for(const [a,b] of[["d_ocd",s.ocd],["d_swo",s.swo],["sb_ocd",s.ocd],["sb_swo",s.swo]])
    $(a).classList.toggle("on",b);
  /* 状态徽标 + 通道 pill（列表没变不重建 DOM） */
  window._pc=s.halt_pc;window._chports=s.chan_ports;window._evport=s.event_port;
  const ps=(s.chan_ports||[]).join(",")+"#"+s.event_port;
  if(window._psSig!==ps){window._psSig=ps;renderPills();}
  window._state=s.tgt_state;
  /* running→halted 瞬间：强制重载 PC 函数窗口并滚动（pollDis 只在
     PC 不在缓存时才 reload，全量缓存已包含 PC 就只标高亮不滚 = 看不到） */
  if(s.tgt_state==="halted"&&window._prevState!=="halted"&&s.halt_pc){
    _disJumpPc=null;_disJumpRun=false;     /* 新 halt = 解锁并定位 */
    disLastPc=null;                        /* 强制触发 scrollIntoView */
    if(tab==="debug"){
      const a=parseInt(s.halt_pc,16);
      disLoad(a,null,$("dissrc").checked).then(()=>{
        const row=document.querySelector(`.drow[data-a="${a}"]`);
        if(row){row.scrollIntoView({block:"center",behavior:"smooth"});}
      });
    }
  }
  window._prevState=s.tgt_state;
  const rb=$("dbgRun");
  if(rb)rb.innerHTML=s.tgt_state==="halted"?"▶ 运行":"⏸ Halt";
  const bcls=s.tgt_state==="halted"?"hlt":s.tgt_state==="running"?"run":"unk";
  const btxt=s.tgt_state==="halted"
    ?`⏸ ${s.halt_reason||"halted"}${s.halt_pc?" @"+s.halt_pc:""}`
    :s.tgt_state==="running"?"▶ 运行中":"—";
  $("t_state").innerHTML=`<span class="b ${bcls}">${esc(btxt)}</span>`;
  $("t_mhz").textContent=s.mhz?s.mhz.toFixed(2)+" MHz":"—";
  $("t_pc").textContent=s.pc_total.toLocaleString();
  $("t_exc").textContent=s.exc_events.toLocaleString();
  $("t_rs").textContent=s.resyncs.toLocaleString();
  $("t_pc_on").checked=s.pc_on;$("t_exc_on").checked=s.exc_on;
  $("t_pc2").checked=s.pc_on;$("t_exc2").checked=s.exc_on;
  $("sb_up").textContent=fmtUp(s.uptime_s);
  $("sb_right").textContent=`${UI_VER} · ${s.elf.split("/").pop()} · ${s.symbols} 符号 · ${s.objects?"+":""}${s.objects||0} 变量 · ovf ${s.overflows.toLocaleString()}`;
  $("elf_path_show").textContent=s.elf;
  push(H.mhz,s.mhz);push(H.exc,s.exc_ps||0);push(H.slp,s.sleep_pct||0);
  if(tab=="dwt")$("g_ovf").textContent=s.overflows.toLocaleString();
  if(m.tab===tab&&m.data!==undefined){
    if(m.tab=="prof")renderProf(m.data);
    else if(m.tab=="exc")renderExc(m.data);
    else if(m.tab=="tl2")renderTl2(m.data);
    else if(m.tab=="dwt")renderDwt(m.data);
    else if(m.tab=="debug")renderDebug(m.data);
    else if(m.tab=="watch")renderWatch(m.data);
  }
  if(tab==="debug")pollDis();   // 反汇编已并入调试页：跟随 PC
  if(tab==="target")pollSyms();
 }catch(e){}}
let _profDis=null,_profIdx=null,_profReq=false,profLast=null;
let _profSig=null,_profRows={};
function profInsn(pc){                 /* 地址→反汇编指令文本（热点直观化） */
 if(!_profDis||!_profDis.rows)return"";
 if(!_profIdx){_profIdx={};
   for(const rr of _profDis.rows)if(rr[0]==="i"&&_profIdx[rr[1]]===undefined)
     _profIdx[rr[1]]=rr[3];}
 return _profIdx[parseInt(pc,16)]||"";}
function renderProf(s){
 if(!_profDis&&!_profReq){_profReq=true;  /* 后台拉全量反汇编（独立缓存，
   不动 disCache——那是调试页窗口定位的状态机），到了重渲 */
   wreq({t:"disasm",src:0}).then(r=>{
     if(!r.error){_profDis=r;_profIdx=null;_profSig=null;  /* 清签名=下次
       重建带指令标注（构建时反汇编可能还没到，指令是空的） */
       if(profLast)renderProf(profLast);}});}
 profLast=s;
 $("p_total").textContent=s.total.toLocaleString();
 $("p_rate").textContent=s.rate_per_s.toLocaleString();
 $("p_elapsed").textContent=s.elapsed_s+" s";
 $("p_sleep").textContent=s.sleep.toLocaleString();
 $("p_hint").textContent=s.total?`top1：${s.top[0].sym}（${s.top[0].pct.toFixed(1)}%）`
   :"未开启——工具栏打开「PC 采样」";
 const mx=Math.max(1,...s.top.map(x=>x.n));
 /* 表格 DOM 只建一次（按地址签名）——8fps innerHTML 重建会把 mousedown
    的节点在 mouseup 前销毁，浏览器不生成 click = "点不中"（实测） */
 const sig=s.top.map(r=>r.pc).join(",");
 const tb=$("p_tbl").querySelector("tbody");
 if(sig!==_profSig){
   _profSig=sig;_profRows={};
   tb.innerHTML=s.top.map((r,i)=>
    `<tr id="pr${i}"><td style="min-width:180px"><div class="bar"><i class="pbar" style="width:0%"></i></div></td>
     <td>${esc(r.sym)}${profInsn(r.pc)?` <span class="mono" style="color:var(--faint)">; ${esc(profInsn(r.pc))}</span>`:""} <span class="cbtn" style="cursor:pointer" data-jump="${r.pc}" title="反汇编定位">⇢</span></td><td class="mono paddr">${r.pc}</td>
     <td class="pcnt">0</td><td class="ppct">0%</td></tr>`).join("")
    ||`<tr><td colspan=5 class="empty">未开启或暂无样本</td></tr>`;
   s.top.forEach((r,i)=>{
     const tr=$("pr"+i);
     if(tr)_profRows[r.pc]={bar:tr.querySelector(".pbar"),
                             cnt:tr.querySelector(".pcnt"),
                             pct:tr.querySelector(".ppct")};});
 }
 s.top.forEach(r=>{                    /* 热路径：只改文本/宽度 */
   const e=_profRows[r.pc];
   if(!e)return;
   e.bar.style.width=(100*r.n/mx)+"%";
   e.cnt.textContent=r.n.toLocaleString();
   e.pct.textContent=r.pct.toFixed(2)+"%";});
 /* 分布条：top6 + 其他 */
 const seg=s.top.slice(0,6);const other=100-seg.reduce((a,x)=>a+x.pct,0);
 $("dist").innerHTML=seg.map((r,i)=>
   `<div style="width:${r.pct}%;background:${DCOLORS[i%8]}" title="${esc(r.sym)} ${r.pct.toFixed(1)}%">${r.pct>=6?esc(r.sym.split("+")[0]):""}</div>`).join("")
  +(s.top.length>6&&other>0.3?`<div style="width:${other}%;background:#33414f" title="其他 ${other.toFixed(1)}%">…</div>`:"");
 $("distleg").innerHTML=seg.map((r,i)=>
   `<span><span style="color:${DCOLORS[i%8]}">■</span> ${esc(r.sym.split("+")[0])} ${r.pct.toFixed(1)}%</span>`).join("");
}
function renderExc(s){
 $("e_events").textContent=s.events.toLocaleString();
 $("e_ret").textContent=s.ret_avg_us??"—";
 $("e_mis").textContent=s.mispaired.toLocaleString();
 $("e_rs").textContent=s.resyncs.toLocaleString();
 $("e_hint").textContent=s.events?`最近事件：${s.recent.length?excName(s.recent[s.recent.length-1].exc):"—"}`
   :"未开启——工具栏打开「异常跟踪」";
 /* 表格建一次（按异常号签名），20fps 只改文本/条宽——
    innerHTML 全量重建会抖（列宽跳+hover 丢失，实测同剖析表） */
 const tb=$("e_tbl").querySelector("tbody");
 const mx=Math.max(1,...s.irqs.map(x=>x.n));
 const esig=s.irqs.map(q=>q.exc).join(",");
 if(esig!==window._excSig){
   window._excSig=esig;window._excRows={};
   tb.innerHTML=s.irqs.map((q,i)=>
    `<tr id="er${i}"><td style="min-width:140px"><div class="bar"><i class="ebar" style="width:0%"></i></div></td>
     <td class="mono">${q.exc}</td><td>${esc(excName(q.exc))}</td><td class="ecnt">0</td>
     <td class="eh">—</td><td class="et">—</td><td class="ep">—</td></tr>`).join("")
    ||`<tr><td colspan=7 class="empty">未开启或暂无事件</td></tr>`;
   s.irqs.forEach((q,i)=>{
     const tr=$("er"+i);
     if(tr)window._excRows[q.exc]={bar:tr.querySelector(".ebar"),
       cnt:tr.querySelector(".ecnt"),h:tr.querySelector(".eh"),
       t:tr.querySelector(".et"),p:tr.querySelector(".ep")};});
 }
 s.irqs.forEach(q=>{
   const e=window._excRows[q.exc];if(!e)return;
   e.bar.style.width=(100*q.n/mx)+"%";
   e.cnt.textContent=q.n.toLocaleString();
   e.h.textContent=(q.h_avg_us??"—")+" / "+q.h_max_us;
   e.t.textContent=q.t_avg_us??"—";
   e.p.textContent=q.p_avg_us??"—";});
 /* 时间线：按异常号分 lane */
 const ev=s.recent;
 if(!ev.length){$("tl_lanes").innerHTML=`<div class="empty" style="padding:10px">暂无事件</div>`;
   $("tlx0").textContent=$("tlx1").textContent="";return;}
 const t0=ev[0].ms,t1=ev[ev.length-1].ms,span=(t1-t0)||1e-3;
 const lanes=[...new Set(ev.map(e=>e.exc))].slice(0,5);
 $("tl_lanes").innerHTML=lanes.map(ex=>{
   const marks=ev.filter(e=>e.exc===ex||e.k==="ret").map(e=>
     `<div class="ev ${e.k}" style="left:calc(${((e.ms-t0)/span*100).toFixed(2)}% - 2px)"
       title="@${e.ms.toFixed(3)}ms ${e.k} #${e.exc} ${esc(excName(e.exc))}"></div>`).join("");
   return `<div class="lane"><span class="axis"></span><span class="lname">${esc(excName(ex))} (#${ex})</span>${marks}</div>`;
 }).join("");
 $("tlx0").textContent=t0.toFixed(2)+" ms";
 $("tlx1").textContent=t1.toFixed(2)+" ms";
}
function renderDwt(s){
 $("g_mhz").textContent=s.mhz.toFixed(2);
 $("g_exc").textContent=s.exc_ps.toFixed(0);
 $("g_slp").textContent=s.sleep_pct.toFixed(1);
 $("g_ovf").textContent="—";
 $("r_cyc").textContent=s.raw.cyc;
 for(const k of["cpi","exc","slp","lsu","fold"])$("r_"+k).textContent=s.raw[k];
 spark("c_mhz",H.mhz,"#43c983");spark("c_exc",H.exc,"#4fc3f7");spark("c_slp",H.slp,"#e6b35a");
}
let symsCache=null;
let _symRendered=false;
async function pollSyms(){
 if(_symRendered)return;               // 表只渲染一次：20fps 重建 innerHTML
 if(!symsCache){symsCache=await wreq({t:"sym"});}  // 会把按钮换掉→click 落在死
 if(!symsCache||symsCache.error)return;             // 元素上（＋监控点了没反应）
 _symRendered=true;
 $("elf_info").textContent=`${symsCache.elf} · ${symsCache.count} 符号`;
 const tb=$("sy_tbl").querySelector("tbody");
 tb.innerHTML=symsCache.syms.map(r=>
   `<tr><td class="mono">${r.a}</td><td>${r.sz}</td><td>${esc(r.n)}${r.t==="O"?
    ` <button class="cbtn" style="margin-left:6px" onclick="symWatch('${esc(r.n)}')">＋监控</button>`:""}</td></tr>`).join("");
}
/* ================= 调试：寄存器 / 内存 / 断点 ================= */
let lastRegs={};
function rnum(n){const m=n.match(/^r(\d+)$/i);return m?+m[1]:99;}
function renderDebug(s){
 try{
  $("dbgreason").textContent=
    s.state==="halted"?`${s.reason||"halted"} @${s.pc||"??"}`
    :s.state==="running"?"运行中——Halt 后显示":"jtag_tool 未连（板上先停 openocd，tmux 跑 jtag_tool --serve）";
  const g=$("reggrid");
  if(s.state!=="halted"||!Object.keys(s.regs).length){
    g.innerHTML=`<span class="hint">${s.state==="running"?"目标运行中——工具栏 Halt 后显示寄存器快照":"无寄存器快照"}</span>`;
    lastRegs={};
  }else{
    const keys=Object.keys(s.regs).sort((a,b)=>rnum(a)-rnum(b)||a.localeCompare(b));
    let html=keys.map(k=>{
      const chg=lastRegs[k]!==undefined&&lastRegs[k]!==s.regs[k];
      return `<div class="rg${chg?" chg":""}"><span class="n">${esc(k)}</span><span class="v">${s.regs[k]}</span></div>`;
    }).join("");
    const xk=keys.find(k=>/^xpsr$/i.test(k));
    if(xk){const x=parseInt(s.regs[xk],16);
      const fl=[["N",31],["Z",30],["C",29],["V",28]].map(([n,b])=>
        `<span class="flag${(x>>>b)&1?" on":""}">${n}</span>`).join("");
      const ipsr=x&0x1ff;
      html=`<div class="regwide">${s.regs[xk]}&nbsp; ${fl} <span style="color:var(--dim)">IPSR=${ipsr}（${ipsr?excName(ipsr):"Thread"}）</span></div>`+html;}
    g.innerHTML=html;lastRegs={...s.regs};
  }
 }catch(e){}}
async function tgtToggle(){
  const r=await post("/api/target",
    {action:(window._state==="halted")?"resume":"halt"});
  if(r.error)$("dbgbarInfo").textContent=r.error;}
async function stepN(n){const r=await post("/api/step",{n});
  if(r.error){$("dbgreason").textContent=r.error;return;}
}

let memBase=null,memW=4;
async function memGo(){
 const a=$("memaddr").value.trim();if(!a)return;
 $("meminfo").textContent="…";
 const r=await wreq({t:"mem",addr:a,len:parseInt($("memlen").value)||64,w:parseInt($("memw").value)||4});
 if(r.error){$("meminfo").textContent=r.error;return;}
 memBase=parseInt(r.addr,16);memW=r.w;
 $("meminfo").textContent=`${r.addr} 起 ${r.vals.length} 单元`;
 renderMem(r.vals,r.ascii);}
function renderMem(vals,ascii){
 const per=8;let rows="";
 for(let i=0;i<vals.length;i+=per){
  const row=vals.slice(i,i+per);
  const arow=ascii.slice(i*per*memW,(i+1)*per*memW);
  rows+=`<tr><td class="a">0x${(memBase+i*per*memW).toString(16).padStart(8,"0")}</td>`+
   row.map((v,j)=>`<td class="c" onclick="memEdit(${i*per+j},this)">${v}</td>`).join("")+
   `<td class="a">${esc(arow)}</td></tr>`;}
 $("memh").textContent=`值（点击编辑 · ${memW===4?"字":memW===2?"半字":"字节"}）`;
 $("memtbl").querySelector("tbody").innerHTML=rows;}
function memEdit(idx,td){
 if(memBase===null)return;
 const addr="0x"+(memBase+idx*memW).toString(16);
 const v=prompt(`${addr} 新值（hex/dec）：`,td.textContent.trim());
 if(v===null||v==="")return;
 post("/api/mem",{addr,w:memW,value:v}).then(r=>{
   if(r.error)alert(r.error);else memGo();});}
/* 内存浏览器一键加入变量监控：字宽映射格式（4→u32 2→u16 1→u8），
 * 符号名/0x 地址皆可（输入框带 STT_OBJECT 自动补全） */
async function memWatch(){
 const a=$("memaddr").value.trim();
 if(!a){$("meminfo").textContent="先填地址或符号";return;}
 const fmt={"4":"u32","2":"u16","1":"u8"}[$("memw").value]||"u32";
 const r=await post("/api/watch",{action:"add",name:a,fmt});
 if(r.error)alert(r.error);
 else $("meminfo").textContent=`${a}（${fmt}）已加入「变量」页`;}
async function symWatch(n){
 const r=await post("/api/watch",{action:"add",name:n,fmt:"u32",win:0});
 if(r.error)alert(r.error);
 else $("elf_info").textContent=`${n} 已加入「变量」页（格式可在表格里改）`;}
async function bpAdd(){
 const sel=$("bpkind").value,kind=sel.startsWith("bp")?"bp":"wp";
 const o={action:"add",kind,addr:$("bpaddr").value.trim(),
   len:sel==="bp4"?4:(kind==="wp"?4:2)};
 if(kind==="wp")o.acc=sel==="wpr"?"r":sel==="wpw"?"w":"a";
 const r=await post("/api/bp",o);
 $("bpout").textContent=r.out||r.error||"";
  if(r.bps){bpsCache={bps:r.bps,wps:r.wps||[]};renderBps();disRender();}}
async function bpDel(kind,addr){const r=await post("/api/bp",{action:"del",kind,addr});
  if(r.bps){bpsCache={bps:r.bps,wps:r.wps||[]};renderBps();disRender();}}
async function bpClr(){const r=await post("/api/bp",{action:"clr"});
  if(r.bps){bpsCache={bps:r.bps,wps:r.wps||[]};renderBps();disRender();}}
let bpsCache={bps:[],wps:[]};
function renderBps(){
  const s=bpsCache;
  if(s.error)return;
  $("bp_tbl").querySelector("tbody").innerHTML=
   s.bps.map(b=>`<tr><td>断点${b.hw?" hw":""}</td><td class="mono">${b.addr}</td><td>${b.len}</td><td>—</td>
     <td><button class="cbtn" onclick="bpDel('bp','${b.addr}')">删</button></td></tr>`).join("")+
   s.wps.map(w=>`<tr><td>观察点 ${w.acc}</td><td class="mono">${w.addr}</td><td>${w.len||"—"}</td><td>—</td>
     <td><button class="cbtn" onclick="bpDel('wp','${w.addr}')">删</button></td></tr>`).join("")
   ||`<tr><td colspan=5 class="empty">无</td></tr>`;
}

/* ================= 反汇编 ================= */
let disCache=null,disLastPc=null,disFuncsLoaded=false;
async function loadFuncs(){
 const r=await wreq({t:"disfuncs"});
 if(r.error){$("disinfo").textContent=r.error;return;}
 $("dfuncs").innerHTML=r.funcs.map(f=>
  `<div onclick="disFuncSel('${f.n.replace(/'/g,"\\'")}')">${esc(f.n)} <span style="color:var(--faint)">${f.sz}B</span></div>`).join("")
  ||`<div class="empty" style="padding:10px">无函数（先在「目标」页加载 ELF）</div>`;}
async function disFuncSel(n){
 showTab("debug");
 const f=await disLoad(null,n,$("dissrc").checked);
 [...$("dfuncs").children].forEach(d=>d.classList.toggle("on",d.textContent.startsWith(n)));}
async function disLoad(addr,name,src){
 const q=src?"&src=1":"";
 const r=await wreq(name!=null?{t:"disasm",func:name,src:src?1:0}
   :{t:"disasm",addr:"0x"+addr.toString(16),src:src?1:0});
 if(r.error){$("disinfo").textContent=r.error;return null;}
 disCache=r;
 disRender();
 return r.func;}
function disBPAt(a){return bpsCache.bps.some(b=>parseInt(b.addr,16)===a);}
async function fetchBps(){
 try{const r=await(await fetch("/api/bps")).json();
   if(r.bps){bpsCache={bps:r.bps,wps:r.wps||[]};renderBps();disRender();}}catch(e){}}
async function disBP(a,el){
 /* FP_COMP 存字基址（半字选择在高位）：列表回读地址可能比指令地址小 2，
   按字对齐匹配已有断点、按列表地址删——否则每击都"新增"堆比较器 */
 const ex=bpsCache.bps.find(b=>(parseInt(b.addr,16)&~3)===(a&~3));
 const r=await post("/api/bp",ex?{action:"del",kind:"bp",addr:ex.addr}
                                :{action:"add",kind:"bp",addr:`0x${a.toString(16)}`,len:2});
 const has=!!ex;
 const now=!has&&!(r&&r.error);            /* 成功后的新状态 */
 if(r.bps){bpsCache={bps:r.bps,wps:r.wps||[]};renderBps();}
 if(el){el.textContent=now?"●":"○";el.classList.toggle("on",now);}  /* 原地翻转：
   不全量 disRender——DOM 重建会吞掉紧随的第二次点击（toggle 不稳） */}
function disRender(){
 if(!disCache||!disCache.rows)return;
 let html="";
 for(const r of disCache.rows){
  if(r[0]==="f")html+=`<div class="drow fn">${esc(r[1])} @ 0x${r[2].toString(16)}</div>`;
  else if(r[0]==="s")html+=`<div class="drow src">${esc(r[1])}</div>`;
  else html+=`<div class="drow" data-a="${r[1]}"><span class="dgp${disBPAt(r[1])?" on":""}" onclick="disBP(${r[1]},this)" title="断点增删">${disBPAt(r[1])?"●":"○"}</span><span class="da">0x${r[1].toString(16).padStart(8,"0")}</span><span class="db">${esc(r[2])}</span>${esc(r[3])}</div>`;}
 $("dpre").innerHTML=html;
 disPcMark();}
function disPcMark(){
 document.querySelectorAll(".drow.pchit").forEach(e=>e.classList.remove("pchit"));
 const pc=window._pc;
 if(!pc||!disCache)return;
 const row=document.querySelector(`.drow[data-a="${parseInt(pc,16)}"]`);
 if(row)row.classList.add("pchit");}
async function pollDis(){
 if(_disBusy)return;                         /* disReload 中：别抢 */
 if(_disJumpRun&&!window._pc)return;         /* 运行中跳转：纯浏览，不自动加载 */
 if(_disJumpRun&&window._pc)_disJumpRun=false; /* halt 了：解锁跟随 */
 if(_disJumpPc&&window._pc===_disJumpPc)return;  /* halt 态跳转，PC 未变：保持 */
 if(_disJumpPc&&window._pc!==_disJumpPc)_disJumpPc=null; /* PC 变：解锁 */
 if(!disFuncsLoaded){disFuncsLoaded=true;loadFuncs();fetchBps();}
 if(!disCache){
   if(window._pc){await disLoad(parseInt(window._pc,16),null,$("dissrc").checked);return;}
   /* 运行中无 PC：加载全量反汇编——断点随时可下（空面板点不了是坑） */
   const r=await wreq({t:"disasm",src:$("dissrc").checked?1:0});
   if(!r.error&&r.rows){disCache=r;disRender();}
   return;}
 if(!window._pc)return;
 const a=parseInt(window._pc,16);
 const has=disCache.rows.some(r=>r[0]==="i"&&r[1]===a);
 if(!has){
   const f=await disLoad(a,null,$("dissrc").checked);
   if(f)$("disinfo").textContent=`${f.n} · PC ${window._pc}`;
 }else disPcMark();
 if(window._pc!==disLastPc){disLastPc=window._pc;
   const row=document.querySelector(`.drow[data-a="${a}"]`);
   if(row)row.scrollIntoView({block:"center"});}}
let _disJumpPc=null,_disJumpRun=false;
/* 跳转锁两态：
   运行中跳转 → _disJumpRun=true，pollDis 全返回（无 PC 可跟，纯浏览）
   halt 态跳转 → _disJumpPc=pc，PC 不变就不拉走；变了（单步/断点）解锁 */
function disJump(t){
 t=(t||"").trim();if(!t)return;
 showTab("debug");
 if(window._pc)_disJumpPc=window._pc;   /* halt 态：锁 PC */
 else{_disJumpRun=true;_disJumpPc=null;} /* 运行中：纯浏览锁 */
 if(!disFuncsLoaded){disFuncsLoaded=true;loadFuncs();}
 if(/^0x/i.test(t)){
   disLastPc=null;
   const a=parseInt(t,0);
   _disFocusAddr=a;                   /* 记住目标地址，源码切换后重定位用 */
   disLoad(a,null,$("dissrc").checked).then(()=>{
     /* 跳转地址高亮+滚动（pollDis 只跟 halt PC，运行中不滚 = 剖析
        页跳转看起来"没反应"的根因） */
     const row=document.querySelector(`.drow[data-a="${a}"]`);
     if(row){
       document.querySelectorAll(".drow.pchit").forEach(e=>e.classList.remove("pchit"));
       row.classList.add("pchit");
       row.scrollIntoView({block:"center",behavior:"smooth"});
       $("disinfo").textContent=`定位 0x${a.toString(16)}`;
     }
   });
 }else disLoad(null,t,$("dissrc").checked);}
function jumpPcDis(){if(!window._pc){alert("目标未停止，无 PC");return;}disJump(window._pc);}
let _disBusy=false;    /* disReload 进行中：pollDis 不抢 */
let _disFocusAddr=null; /* 用户跳转/查看的目标地址——切源码交错后按此重定位 */
async function disReload(){
 _disBusy=true;
 const lastFunc=disCache&&disCache.func?disCache.func.n:null;
 const focus=_disFocusAddr;             /* 用户在看哪条指令 */
 /* 不清跳转锁！——清了之后 pollDis 会在 _disBusy 释放后 50ms 内
    因 halt PC 不在窗口而拉走 = "定位又变了"（实测） */
 disCache=null;disLastPc=null;disFuncsLoaded=true;
 try{
   await loadFuncs();
   if(lastFunc){
     const r=await wreq({t:"disasm",func:lastFunc,src:$("dissrc").checked?1:0});
     if(!r.error){disCache=r;disRender();
       /* 按记住的地址重新定位到同一条指令 */
       if(focus!=null){
         const row=document.querySelector(`.drow[data-a="${focus}"]`);
         if(row){
           document.querySelectorAll(".drow.pchit").forEach(e=>e.classList.remove("pchit"));
           row.classList.add("pchit");
           row.scrollIntoView({block:"center"});
         }
       }
     }
     return;
   }
   const t=$("disjump").value.trim();
   if(t)disJump(t);else if(window._pc)pollDis();
   else{
     const r=await wreq({t:"disasm",src:$("dissrc").checked?1:0});
     if(!r.error&&r.rows){disCache=r;disRender();}
   }
 }finally{_disBusy=false;}
}

/* ================= 变量 watch：五视图 + 阈值触发 ================= */
let wData=null,wDisp=null;      // wData=最新数据；wDisp=显示数据（暂停/触发冻结脱钩）
let wFrozenOk=false;            // 冻结快照已建（wDisp 不与 wCache 共享数组）
let wCache={},wCacheSig=null;   // 服务端增量推送的客户端合并缓存
let wModeV="line",wPaused=false;
const wTrig={on:false,fired:false,var:"",cmp:">",v:0,t0:0};
let _wsig="";
const _f32b=new ArrayBuffer(4),_f32u=new Uint32Array(_f32b),_f32f=new Float32Array(_f32b);
const _f64b=new ArrayBuffer(8),_f64u=new Uint32Array(_f64b),_f64f=new Float64Array(_f64b);
function wNum(w,v){             // 原始 u 值 -> 按 fmt 的数值
  if(v==null)return null;
  switch(w.fmt){
    case"i32":return v|0;
    case"u16":return (v>>>0)&0xFFFF;
    case"i16":{const x=v&0xFFFF;return x>=0x8000?x-0x10000:x;}
    case"u8":return (v>>>0)&0xFF;
    case"i8":{const x=v&0xFF;return x>=0x80?x-0x100:x;}
    case"f32":_f32u[0]=v>>>0;return _f32f[0];
    case"u64":return Number(v);        /* JS Number 精确到 2^53 够用 */
    case"i64":return v>0x7FFFFFFFFFFFFF?v-0x10000000000000000:Number(v);
    case"f64":_f64u[0]=v&0xFFFFFFFF;_f64u[1]=Math.floor(v/0x100000000);return _f64f[0];
    default:return v>>>0;}}
function wStr(w,v){const x=wNum(w,v);return x==null?"—":
  w.fmt==="f32"?x.toFixed(4):w.fmt==="f64"?x.toFixed(6):
      w.fmt==="hex"?"0x"+x.toString(16):String(x);}
async function watchAdd(){
 const n=$("wname").value.trim();if(!n)return;
 const r=await post("/api/watch",{action:"add",name:n,fmt:$("wfmt").value});
 $("winfo").textContent=r.error||`已添加 ${n}`;
 if(!r.error){$("wname").value="";wTrig.fired=false;wDisp=null;wFrozenOk=false;}}
async function watchRate(){
 const r=await post("/api/watch",{action:"rate",ms:parseInt($("wrate").value)||500});
 $("winfo").textContent=r.error||`采样周期 ${r.watch_ms}ms`;}
async function watchDel(n){await post("/api/watch",{action:"del",name:n});}
async function wFmtSet(n,f){
  const r=await post("/api/watch",{action:"setfmt",name:n,fmt:f});
  $("winfo").textContent=r.error||`${n} 格式 → ${f}`;}
async function wWinSet(n,k){
  const r=await post("/api/watch",{action:"setwin",name:n,win:parseInt(k)});
  $("winfo").textContent=r.error||`${n} → 波形窗${k}`;}
async function watchClr(){await post("/api/watch",{action:"clr"});wTrig.fired=false;wDisp=null;wFrozenOk=false;}
function wMode(m){wModeV=m;
 document.querySelectorAll("#wtabs button").forEach(b=>b.classList.toggle("on",b.dataset.m===m));
 drawW();}
function wPause(p){wPaused=p;
 if(!p&&!wTrig.fired){wDisp=null;wFrozenOk=false;}   // 解冻回实时
 drawW();}
function wTrigToggle(){
 if(wTrig.on&&wTrig.fired){          // 触发后再点 = 取消触发，回实时
   wTrig.on=false;wTrig.fired=false;wTrig.capEnd=0;
   wDisp=null;wFrozenOk=false;
   $("wtrigbtn").textContent="触发：关";drawW();return;}
 wTrig.on=!wTrig.on;wTrig.fired=false;
 wTrig.var=$("wtrigvar").value;wTrig.cmp=$("wtrigcmp").value;
 wTrig.v=parseFloat($("wtrigv").value)||0;
 if(wTrig.on){wDisp=null;wFrozenOk=false;}
 $("wtrigbtn").textContent=wTrig.on?"触发：武装":"触发：关";
 drawW();}
function fillTrigSels(){
 const sig=(wDisp?wDisp.watches.map(w=>w.name).join(","):"");
 if(sig===_wsig)return;
 _wsig=sig;
 const opts=wDisp?wDisp.watches.map(w=>`<option>${esc(w.name)}</option>`).join(""):"";
 const tv=$("wtrigvar");
 const kT=tv.value;
 tv.innerHTML=opts;
 if(kT)tv.value=kT;}
function wRange(w){
 let lo=Infinity,hi=-Infinity;
 for(const p of w.series){const v=wNum(w,p[1]);if(v==null)continue;
   lo=Math.min(lo,v);hi=Math.max(hi,v);}
 if(lo>hi)return[0,1];if(lo===hi)return[lo-1,hi+1];return[lo,hi];}
let _wsigUI=null,wRows={};
function renderWatch(s){
 try{
  /* 增量合并：full 或新变量=重建，其余追加（本地镜像 600 点） */
  const sig=s.watches.map(w=>w.name+"|"+w.fmt+"|"+(w.win??1)).join(",");
  if(sig!==wCacheSig){wCacheSig=sig;wCache={};}
  const list=s.watches.map(w=>{
    let c=wCache[w.name];
    if(!c||w.full)
      c={name:w.name,addr:w.addr,size:w.size,fmt:w.fmt,win:w.win??1,series:w.pts.slice()};
    else for(const p of w.pts){
      c.series.push(p);if(c.series.length>600)c.series.shift();}
    wCache[w.name]=c;return c;});
  s={watches:list};
  wData=s;
  /* 触发状态机：武装→(命中,记 t0)→采集中(live 继续)→采满后半窗→定格 */
  if(wTrig.on&&!wTrig.fired){
    const w=s.watches.find(x=>x.name===wTrig.var);
    const cur=w&&w.series.length?wNum(w,w.series[w.series.length-1][1]):null;
    if(cur!=null&&(wTrig.cmp===">"?cur>wTrig.v:cur<wTrig.v)){
      wTrig.fired=true;
      wTrig.t0=w.series[w.series.length-1][0];
      const tb=parseFloat($("wtb").value)||0;
      wTrig.capEnd=wTrig.t0+(tb>0?tb/2:1.0);
      $("wtrigbtn").textContent="触发：采集中…";}}
  let latest=-Infinity;
  for(const w of s.watches)if(w.series.length)
    latest=Math.max(latest,w.series[w.series.length-1][0]);
  const capDone=wTrig.fired&&latest>=wTrig.capEnd;   // 后半窗采满
  if(!wPaused&&!capDone){wDisp=s;wFrozenOk=false;}    // 采集中=live 滚动
  else if(!wFrozenOk){          // 定格瞬间：拷贝数组快照（win 必须带上，
    wDisp={watches:s.watches.map(w=>({name:w.name,addr:w.addr,size:w.size,
      fmt:w.fmt,win:w.win??1,series:w.series.slice()}))};
    wFrozenOk=true;
    if(capDone)$("wtrigbtn").textContent="TRIG'D（点按取消）";}
  if(sig!==_wsigUI){                 // 列表变更才重建 DOM（结构/图例/存储）
    _wsigUI=sig;wRows={};
    localStorage.setItem("swo_watches",sig.split(",").join("\n"));
    const tb=$("w_tbl").querySelector("tbody");
    tb.innerHTML=s.watches.map((w,i)=>{
      const[lo,hi]=wRange(w);
      const fsel=["u32","i32","hex","u16","i16","u8","i8","f32","u64","i64","f64"].map(f=>
        `<option${f===w.fmt?" selected":""}>${f}</option>`).join("");
      const wsel=[1,2,3,4].map(k=>
        `<option value="${k}"${(w.win??1)===k?" selected":""}>窗${k}</option>`).join("")+
        `<option value="0"${(w.win||0)===0?" selected":""}>不显示</option>`;
      return `<tr id="wr${i}"><td><span style="color:${DCOLORS[i%8]}">■</span></td><td>${esc(w.name)}</td>
      <td class="mono">${w.addr}</td><td><select style="width:58px" onchange="wFmtSet('${esc(w.name)}',this.value)">${fsel}</select></td>
      <td><select style="width:56px" onchange="wWinSet('${esc(w.name)}',this.value)">${wsel}</select></td><td class="mono cur">—</td>
      <td class="mono lo">${fmtY(lo,w.fmt==="f32")}</td><td class="mono hi">${fmtY(hi,w.fmt==="f32")}</td><td class="cnt">0</td>
      <td><button class="cbtn" onclick="watchDel('${w.name}')">删</button></td></tr>`;}).join("")
     ||`<tr><td colspan=10 class="empty">无 watch</td></tr>`;
    s.watches.forEach((w,i)=>{
      const tr=$("wr"+i);
      if(tr)wRows[w.name]={cur:tr.querySelector(".cur"),
                           cnt:tr.querySelector(".cnt"),
                           lo:tr.querySelector(".lo"),hi:tr.querySelector(".hi")};});
    $("wleg").innerHTML=s.watches.map((w,i)=>
      `<span><span style="color:${DCOLORS[i%8]}">■</span> ${esc(w.name)}（${w.fmt}）</span>`).join("");
    fillTrigSels();
  }else{                             // 20fps 热路径：仅原地更新文本
    for(const w of s.watches){
      const r=wRows[w.name];if(!r)continue;
      const ser=w.series,cur=ser.length?ser[ser.length-1][1]:null;
      const[lo,hi]=wRange(w);
      r.cur.textContent=wStr(w,cur);
      r.cnt.textContent=ser.length;
      r.lo.textContent=fmtY(lo,w.fmt==="f32");r.hi.textContent=fmtY(hi,w.fmt==="f32");}
  }
  drawW();
 }catch(e){}}
function fmtY(v,fl){
 if(fl){if(Math.abs(v)<1e-4)return"0";                       /* 近零残留→0 */
   return Number(Number(v).toPrecision(3)).toString();}      /* 浮点 3 位有效 */
 if(Math.abs(v)>=1e7)return(v/1e6).toFixed(0)+"M";           /* 整型无小数点 */
 return String(Math.round(v));}
function fmtT(t){return new Date(t*1000).toTimeString().slice(0,8);}
function wCanvas(h){
 const cv=$("wchart"),W=cv.clientWidth||900;
 if(cv.width!==W*2||cv.height!==h*2){cv.width=W*2;cv.height=h*2;}
 cv.style.height=h+"px";
 const x=cv.getContext("2d");x.setTransform(2,0,0,2,0,0);x.clearRect(0,0,W,h);
 return[cv,x,W,h];}
function wEmpty(x,msg){x.fillStyle=cvc("#5b6b7c","#66778a");x.font="12px monospace";x.fillText(msg,14,24);}
function drawW(){
 const s=wDisp;if(!s)return;
 if(wModeV==="gauge")drawGauge(s);
 else if(wModeV==="bits")drawBits(s);
 else if(wModeV==="hist")drawHist(s);
 else drawLine(s);
 if(wModeV==="line")wHoverRender();}
/* ---- 曲线（示波器式：固定时基滑窗 + 刻度网格，波形保持形状左移） ---- */
function wTbSave(v){localStorage.setItem("swo_wtb",v);}
function drawLine(s){
 const tb=parseFloat($("wtb").value)||0;        // 0 = 全部历史
 const ws=s.watches;
 if(!ws.length||!ws.some(w=>w.series.length)){const[c,x]=wCanvas(120);wEmpty(x,"添加全局变量（ELF 符号）后此处画时间曲线");return;}
 /* 全部设为"不显示"（win=0）→ 不画窗口，显示提示（表格数据继续更新） */
 if(!ws.some(w=>(w.win??1)>0)){const[c,x]=wCanvas(60);wEmpty(x,"所有变量已设为「不显示」——表格中数据继续实时更新");return;}
 let t1=-Infinity,t0all=Infinity;
 for(const w of ws)for(const pt of w.series){
   t1=Math.max(t1,pt[0]);t0all=Math.min(t0all,pt[0]);}
 if(!isFinite(t1)){const[c,x]=wCanvas(120);wEmpty(x,"采样中……");return;}
 t1=Math.max(t1,t0all+0.2);
 let t0;
 if(wTrig.fired&&tb>0){                         // 已触发定格：触发点居中
   t0=wTrig.t0-tb/2;t1=wTrig.t0+tb/2;}
 else t0=tb>0?t1-tb:t0all;                      // 常态：固定时基滑窗
 /* 分窗：各窗口独立 Y 量程，共享时基 */
 const wins={};
 for(const w of ws){const k=w.win??1;if(k===0)continue;(wins[k]=wins[k]||[]).push(w);}
 const keys=Object.keys(wins).map(Number).sort((a,b)=>a-b);
 const nw=keys.length;
 const NY=nw>1?4:8;                              // 多窗时纵向 4 格
 const H=nw>1?Math.min(205*nw,820):300;
 const[cv,x,W,Hh]=wCanvas(H);
 const fmtT2=s2=>{const a=Math.abs(s2);
   return a>=1?(Math.round(s2*10)/10)+"s":(Math.round(s2*100))+"ms";};
 const bands=[];
 keys.forEach((k,wi)=>{
  const GAP=18,titleH=22,bandH=(Hh-GAP*(nw-1))/nw,y0=wi*(bandH+GAP);
  const bt=y0+titleH+6,bb=y0+bandH;              // 标题行独立于绘图区
  bands.push({bt,bb,vars:wins[k]});
  if(wi>0){                                      // 窗口分隔条（整宽粗线）
    const sy=y0-GAP/2+2;
    x.strokeStyle=cvc("#3d4f63","#9fb0c0");x.lineWidth=2;
    x.beginPath();x.moveTo(0,sy);x.lineTo(W,sy);x.stroke();
    x.lineWidth=1;}
  const pad={l:56,r:18,t:bt,b:Hh-bb};
  let v0=Infinity,v1=-Infinity;
  for(const w of wins[k])for(const pt of w.series){if(pt[0]<t0)continue;
    const v=wNum(w,pt[1]);if(v==null)continue;
    v0=Math.min(v0,v);v1=Math.max(v1,v);}
  if(v1===v0){v0-=1;v1+=1;}
  const vlo=v0-(v1-v0)*0.08,vhi=v1+(v1-v0)*0.08;
  const X=t=>pad.l+(t-t0)/(t1-t0)*(W-pad.l-pad.r);
  const Y=v=>bb-(v-vlo)/(vhi-vlo)*(bb-bt);
  /* 裁剪到本窗带 */
  x.save();x.beginPath();x.rect(pad.l-46,bt-12,W-pad.l-pad.r+52,bb-bt+14);x.clip();
  const NX=10,pw=W-pad.l-pad.r,ph=bb-bt,dgx=pw/NX,dgy=ph/NY;
  /* MATLAB 风格：实线细网格（grid on） */
  x.strokeStyle=cvc("#1e2b3a","#e4e9ee");x.lineWidth=1;x.setLineDash([]);
  for(let g=1;g<NX;g++){const xx=pad.l+dgx*g;
    x.beginPath();x.moveTo(xx,bt);x.lineTo(xx,bb);x.stroke();}
  for(let g=1;g<NY;g++){const yy=bt+dgy*g;
    x.beginPath();x.moveTo(pad.l,yy);x.lineTo(W-pad.r,yy);x.stroke();}
  /* 中心十字（保留测量基准，弱化） */
  const ccx=pad.l+pw/2,ccy=bt+ph/2;
  x.strokeStyle=cvc("#26364c","#cdd8e2");x.setLineDash([1,3]);
  x.beginPath();x.moveTo(pad.l,ccy);x.lineTo(W-pad.r,ccy);x.stroke();
  x.beginPath();x.moveTo(ccx,bt);x.lineTo(ccx,bb);x.stroke();
  x.setLineDash([]);
  /* 盒式坐标框 + 内侧刻度（MATLAB box on） */
  x.strokeStyle=cvc("#4a5e78","#8fa1b3");x.lineWidth=1.5;
  x.strokeRect(pad.l,bt,pw,ph);
  for(let g=0;g<=NX;g++){const xx=pad.l+dgx*g;
    x.beginPath();x.moveTo(xx,bb);x.lineTo(xx,bb-4);x.stroke();}
  for(let g=0;g<=NY;g++){const yy=bt+dgy*g;
    x.beginPath();x.moveTo(pad.l,yy);x.lineTo(pad.l+4,yy);x.stroke();}
  const bandFl=wins[k].some(w=>w.fmt==="f32");
  /* 序列 */
  wins[k].forEach(w=>{
    x.beginPath();let st=false;
    for(const pt of w.series){if(pt[0]<t0)continue;
      const v=wNum(w,pt[1]);if(v==null)continue;
      const px=X(pt[0]),py=Y(v);st?x.lineTo(px,py):x.moveTo(px,py);st=true;}
    x.strokeStyle=DCOLORS[ws.indexOf(w)%8];x.lineWidth=1.8;x.stroke();});
  /* 触发电平（只在含触发变量的窗口画） */
  if(wTrig.on&&wins[k].some(w=>w.name===wTrig.var)&&wTrig.v>=vlo&&wTrig.v<=vhi){
    const yy=Y(wTrig.v);
    x.strokeStyle="#e6b35a";x.setLineDash([6,4]);
    x.beginPath();x.moveTo(pad.l,yy);x.lineTo(W-pad.r-2,yy);x.stroke();
    x.setLineDash([]);
    x.beginPath();x.moveTo(W-pad.r,yy);
    x.lineTo(W-pad.r-8,yy-4);x.lineTo(W-pad.r-8,yy+4);x.closePath();
    x.fillStyle="#e6b35a";x.fill();}
  /* 触发竖线（所有窗贯通） */
  if(wTrig.fired&&wTrig.t0>=t0&&wTrig.t0<=t1){
    x.strokeStyle="#e05d5d";x.setLineDash([4,3]);
    x.beginPath();x.moveTo(X(wTrig.t0),bt);x.lineTo(X(wTrig.t0),bb);x.stroke();
    x.setLineDash([]);
    x.fillStyle="#e05d5d";                       /* 触发点居中指示 ▼ */
    x.beginPath();x.moveTo(X(wTrig.t0),bt+2);
    x.lineTo(X(wTrig.t0)-5,bt-6);x.lineTo(X(wTrig.t0)+5,bt-6);x.closePath();x.fill();}
  x.restore();
  /* Y 标签（裁剪区外=首字符不再被切；浮点窗 3 位有效/整型窗纯整数） */
  x.fillStyle=cvc("#5b6b7c","#66778a");x.font="10px monospace";
  for(let g=0;g<=NY;g+=(NY<=4?1:2)){
    const v=vhi-(vhi-vlo)*g/NY,yy=bt+dgy*g;
    x.fillText(fmtY(v,bandFl),4,yy+3);}
  /* 窗口标题 + 色样条图例（裁剪区外=不会被切；颜色=全局序号与表格一致） */
  x.textAlign="left";x.font="600 12px monospace";
  x.fillStyle=cvc("#aebfce","#2c3d4f");
  x.fillText(`窗 ${k}`,pad.l+2,y0+16);
  let lx=pad.l+56;
  x.font="12px monospace";
  wins[k].forEach(w=>{
    const gi=ws.indexOf(w);
    x.strokeStyle=DCOLORS[gi%8];x.lineWidth=3;
    x.beginPath();x.moveTo(lx,y0+11);x.lineTo(lx+16,y0+11);x.stroke();
    x.lineWidth=1.6;
    x.fillStyle=cvc("#c4d1dd","#37485a");
    x.fillText(w.name,lx+21,y0+16);
    lx+=21+x.measureText(w.name).width+16;});
  /* 时间标签 & 读数：最顶窗读数、最底窗时间轴 */
  if(wi===0){
    x.textAlign="left";
    x.fillStyle=cvc("#5b6b7c","#66778a");
    x.fillText(tb>0?fmtT2((t1-t0)/NX)+"/div":"全部历史",pad.l,y0+11-14<0?4:y0-3);
    if(wTrig.on){
      x.fillStyle=wTrig.fired?"#e05d5d":"#e6b35a";
      const tag=(wTrig.cmp===">"?"↑":"↓")+" "+wTrig.v;
      x.fillText(wTrig.fired?`TRIG'D ${tag}`:`TRIG ${tag}`,W-pad.r-110,y0-3>0?y0-3:10);}}
  if(wi===nw-1){
    x.fillStyle=cvc("#5b6b7c","#66778a");x.font="10px monospace";
    const step=(tb>0&&(t1-t0)/NX>=0.4)?2:1;
    x.textAlign="center";
    for(let g=0;g<=NX;g+=step){
      const tt=t0+(t1-t0)*g/NX;
      x.fillText(fmtT2(tt-t1),pad.l+dgx*g,Hh-4);}
    x.textAlign="left";}
 });
 cv._lineMode=true;
 cv._bands=bands;
 cv._geom={t0,t1,pad:{l:56,r:18,t:16,b:Hh-16},W};}
/* ---- 仪表盘 ---- */
function drawGauge(s){
 const ws=s.watches;
 if(!ws.length){const[c,x]=wCanvas(80);wEmpty(x,"添加变量后此处显示仪表盘");return;}
 const cols=Math.min(4,ws.length),rows=Math.ceil(ws.length/cols);
 const[cv,x,W,H]=wCanvas(rows*170+10);
 ws.forEach((w,i)=>{
  const col=i%cols,row=(i/cols)|0;
  const cw=W/cols,cx=col*cw+cw/2,cy=row*170+85,R=Math.min(cw/2,170/2)-24;
  const[lo,hi]=wRange(w);
  const cur=w.series.length?wNum(w,w.series[w.series.length-1][1]):null;
  const frac=cur==null?0:Math.max(0,Math.min(1,(cur-lo)/(hi-lo||1)));
  const a0=Math.PI*0.75,a1=Math.PI*2.25,na=a0+(a1-a0)*frac;
  x.strokeStyle=cvc("#232e3b","#c8d3dd");x.lineWidth=8;
  x.beginPath();x.arc(cx,cy,R,a0,a1);x.stroke();
  x.strokeStyle=DCOLORS[i%8];
  x.beginPath();x.arc(cx,cy,R,a0,na);x.stroke();
  x.strokeStyle=cvc("#dfe8f1","#22303d");x.lineWidth=1.5;
  x.beginPath();
  x.moveTo(cx+Math.cos(na)*(R-11),cy+Math.sin(na)*(R-11));
  x.lineTo(cx+Math.cos(na)*(R+7),cy+Math.sin(na)*(R+7));x.stroke();
  x.textAlign="center";
  x.fillStyle=cvc("#e8eef4","#22303d");x.font="600 15px monospace";
  x.fillText(cur==null?"—":wStr(w,cur),cx,cy+6);
  x.font="10.5px monospace";x.fillStyle=cvc("#8fa0b0","#4a5c6e");
  x.fillText(w.name.slice(0,24),cx,cy+R+14);
  x.fillStyle=cvc("#5b6b7c","#66778a");
  x.fillText(fmtY(lo,w.fmt==="f32"),cx-R,cy+R+14);x.fillText(fmtY(hi,w.fmt==="f32"),cx+R,cy+R+14);
  x.textAlign="left";});}
/* ---- 位视图 ---- */
function drawBits(s){
 const ws=s.watches;
 if(!ws.length){const[c,x]=wCanvas(80);wEmpty(x,"添加变量后此处显示位分解（实时）");return;}
 const[cv,x,W,H]=wCanvas(ws.length*46+14);
 ws.forEach((w,i)=>{
  const y=14+i*46,n=w.size*8;
  const cur=w.series.length?wNum(w,w.series[w.series.length-1][1]):null;
  const bw=Math.max(8,Math.min(30,Math.floor((W-240)/n)));
  x.font="11px monospace";x.fillStyle=DCOLORS[i%8];
  x.fillText(w.name.slice(0,20),8,y+13);
  x.fillStyle=cvc("#8fa0b0","#4a5c6e");x.font="11px monospace";
  x.fillText(cur==null?"—":wStr(w,cur),8,y+32);
  for(let b=0;b<n;b++){
   const bx=W-12-(n-b)*bw;
   const lit=cur!=null&&((cur>>>b)&1);
   x.fillStyle=lit?DCOLORS[i%8]:cvc("#232e3b","#c8d3dd");
   x.fillRect(bx,y,bw-3,18);
   if(b%8===7){x.fillStyle=cvc("#5b6b7c","#66778a");x.font="9px monospace";
     x.fillText(String(b),bx,y+30);}}});}
/* ---- 直方图 ---- */
function drawHist(s){
 const ws=s.watches.filter(w=>w.series.length>4);
 if(!ws.length){const[c,x]=wCanvas(80);wEmpty(x,"采样中……直方图需要足够样本");return;}
 const cols=Math.min(3,ws.length),rows=Math.ceil(ws.length/cols);
 const[cv,x,W,H]=wCanvas(rows*120+10);
 const BUCKETS=40;
 ws.forEach((w,i)=>{
  const col=i%cols,row=(i/cols)|0;
  const cw=W/cols,ox=col*cw+12,oy=row*120+10,gw=cw-26,gh=76;
  const[lo,hi]=wRange(w);
  const bc=new Array(BUCKETS).fill(0);let N=0;
  for(const p of w.series){const v=wNum(w,p[1]);if(v==null)continue;N++;
    let bi=Math.floor((v-lo)/(hi-lo||1)*BUCKETS);
    bc[Math.max(0,Math.min(BUCKETS-1,bi))]++;}
  const mx=Math.max(1,...bc);
  x.font="11px monospace";x.fillStyle=DCOLORS[i%8];
  x.fillText(`${w.name}（${w.fmt}）`,ox,oy+8);
  bc.forEach((c,b)=>{
    const h=c/mx*gh;
    x.fillStyle=c?"#4fc3f7":cvc("#1a2431","#dbe3ea");
    x.fillRect(ox+b*gw/BUCKETS,oy+12+gh-h,gw/BUCKETS-1.5,h);});
  x.fillStyle=cvc("#5b6b7c","#66778a");x.font="9.5px monospace";
  x.fillText(fmtY(lo,w.fmt==="f32"),ox,oy+gh+26);
  const rt=fmtY(hi,w.fmt==="f32");x.fillText(rt,ox+gw-x.measureText(rt).width,oy+gh+26);
  x.fillText(`N=${N}`,ox+gw/2-10,oy+gh+26);});}
let wHover=null;
$("wchart").addEventListener("mousemove",e=>{
 const cv=$("wchart"),r=cv.getBoundingClientRect();
 wHover={mx:e.clientX-r.left,my:e.clientY-r.top};
 wHoverRender();});
$("wchart").addEventListener("mouseleave",()=>{wHover=null;$("whov").style.display="none";});
/* 只显示鼠标所在窗口的变量；记录鼠标位置，每次推送重渲 = 数值实时刷新 */
function wHoverRender(){
 const cv=$("wchart"),g=cv._geom,hv=wHover,hov=$("whov");
 if(!g||!hv||!cv._lineMode||!cv._bands){hov.style.display="none";return;}
 const band=cv._bands.find(b=>hv.my>=b.bt-10&&hv.my<=b.bb+6);
 if(!band||hv.mx<g.pad.l||hv.mx>g.W-g.pad.r){hov.style.display="none";return;}
 const t=g.t0+(hv.mx-g.pad.l)/(g.W-g.pad.l-g.pad.r)*(g.t1-g.t0);
 let html=`<div style="color:#8fa0b0">@ ${(t-g.t1).toFixed(2)}s</div>`;
 const all=wDisp?wDisp.watches:[];
 band.vars.forEach(w=>{
   let best=null,bd=1e18;
   for(const pt of w.series){const d=Math.abs(pt[0]-t);
     if(d<bd){bd=d;best=pt;}}
   if(best)html+=`<div><span style="color:${DCOLORS[all.indexOf(w)%8]}">■</span> `+
     `${esc(w.name)} = <b>${esc(wStr(w,best[1]))}</b></div>`;});
 hov.innerHTML=html;
 hov.style.display="block";
 hov.style.left=Math.min(hv.mx+14,g.W-170)+"px";
 hov.style.top=(hv.my+10)+"px";}
/* watch 列表恢复（localStorage）+ 符号补全 */
{const l=(localStorage.getItem("swo_watches")||"").split("\n").filter(Boolean);
 for(const e of l){const [n,f,g]=e.split("|");
   if(n)post("/api/watch",{action:"add",name:n,fmt:f||"u32",win:parseInt(g)||1});}
 {const tb=localStorage.getItem("swo_wtb");if(tb!==null)$("wtb").value=tb;}
 wreq({t:"sym"}).then(r=>{
   if(r&&r.syms){
     const objs=r.syms.filter(q=>q.t==="O").map(q=>q.n);
     $("wl_syms").innerHTML=objs.map(n=>`<option value="${esc(n)}">`).join("");}});}
/* ================= 时间线（异常 + ITM 事件归并） ================= */
function renderTl2(s){
 try{
  $("w_ev").textContent=s.events.length;
  $("w_des").textContent=s.desync;$("w_sdr").textContent=s.stamp_drops;
  $("w_evp").textContent=window._evport??2;
  const ev=s.events;
  const box=$("tl2_lanes");
  if(!ev.length){box.innerHTML=`<div class="empty" style="padding:10px">暂无事件（异常跟踪 / 事件流固件未开）</div>`;
    return;}
  const t0=ev[0].ms,t1=ev[ev.length-1].ms,span=(t1-t0)||1e-3;
  const key=e=>e.src==="exc"?"exc:"+e.exc:"evt:"+e.type;
  const lanes=[...new Set(ev.map(key))].slice(0,10);
  box.innerHTML=lanes.map(k=>{
    const isExc=k.startsWith("exc:");
    const marks=ev.filter(e=>key(e)===k).map(e=>{
      const left=`left:calc(${((e.ms-t0)/span*100).toFixed(2)}% - 2px)`;
      return isExc
        ?`<div class="ev ${e.k}" style="${left}" title="@${e.ms.toFixed(3)}ms ${e.k} #${e.exc} ${esc(excName(e.exc))}"></div>`
        :`<div class="ev evt" style="${left}" title="@${e.ms.toFixed(3)}ms 事件${e.type} arg=${e.arg}"></div>`;}).join("");
    const name=isExc?`${excName(+k.slice(4))} (#${k.slice(4)})`:`事件类型 ${k.slice(4)}`;
    return `<div class="lane"><span class="axis"></span><span class="lname">${esc(name)}</span>${marks}</div>`;}).join("");
  const xs=$("tl2x").children;
  xs[0].textContent=t0.toFixed(2)+" ms";
  xs[1].textContent=t1.toFixed(2)+" ms";
 }catch(e){}}

function themeToggle(){
 const l=document.body.classList.toggle("light");
 localStorage.setItem("swo_theme",l?"light":"dark");
 $("themeBtn").textContent=l?"☾":"☀";}
{if(localStorage.getItem("swo_theme")==="light"){
  document.body.classList.add("light");}
 const _tb=document.getElementById("themeBtn");
 if(_tb)_tb.textContent=document.body.classList.contains("light")?"☾":"☀";}
/* 剖析表事件委托：tbody 高频 innerHTML 重建会吞 inline onclick 的
   mousedown→mouseup（节点被换掉）——监听器放 tbody 上永生 */
$("p_tbl").querySelector("tbody").addEventListener("click",e=>{
  const t=e.target;
  
  if(t.classList&&t.classList.contains("cbtn")&&t.dataset&&t.dataset.jump){
    
    disJump(t.dataset.jump);}});
sizeSparks();wsConnect();
if(location.hash.length>1)showTab(location.hash.slice(1));     // 显式 #tab 链接优先
else{const _t=localStorage.getItem("swo_tab");if(_t)showTab(_t);}  // 否则回到上次 tab
</script></body></html>"""


# ---------------------------------------------------------------- main
async def main(port):
    ST.syms, ST.objs, ST.sym_by_name = load_symbols(ST.elf_path)
    server = await asyncio.start_server(handle_http, "0.0.0.0", port)
    asyncio.create_task(swo_loop())
    asyncio.create_task(dwt_loop())
    asyncio.create_task(tgt_loop())
    asyncio.create_task(watch_loop())
    print(f"swo_web: http://0.0.0.0:{port}  elf={ST.elf_path} "
          f"({len(ST.syms)} syms + {len(ST.objs)} objs)  "
          f"board={BOARD_HOST} -> {board_addr(BOARD_HOST)}  "
          f"ocd=:{OCD_PORT}  swo=:{SWO_PORT}",
          flush=True)
    async with server:
        await server.serve_forever()


if __name__ == "__main__":
    if len(sys.argv) > 1:
        BOARD_HOST = sys.argv[1]
    port = int(sys.argv[2]) if len(sys.argv) > 2 else 8080
    if len(sys.argv) > 3:
        ST.elf_path = sys.argv[3]
        ST.syms, ST.objs, ST.sym_by_name = load_symbols(ST.elf_path)
    asyncio.run(main(port))
