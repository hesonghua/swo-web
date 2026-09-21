#!/usr/bin/env python3
"""mock_ocd_test.py -- swo_web 后端离线回归（jtag_tool 二进制协议模拟）。

本机起假 jtag_tool 二进制服务器（命令口 15555 包协议 + SWO 流口 15556），
覆盖：帧编解码/seq、haltinfo 状态机、REG/MEM 二进制读写、BP/WP 增删列、
step、swo_tpiu、CMD 文本、SWO 流（port0 文本 + port2 事件）、断链重连。
"""
import asyncio
import struct
import sys

sys.path.insert(0, "/home/victor/workspace/zynq-linux/boards/ebaz4205_esp32/swo-web")
import swo_web as S

CMD_PORT, SWO_PORT_M = 15555, 15556


class FakeTarget:
    def __init__(self):
        self.halted = False
        self.pc = 0x0800EA62
        self.regs = [i for i in range(13)] + [0x20004EE0, 0x0800F00F,
                   0x0800EA62, 0x61000000, 0x20005000, 0x20004E00,
                   0, 0, 0, 0]
        self.bps = []   # (addr, len)
        self.wps = []   # (addr, len, acc)


TG = FakeTarget()
REGS_BY_SEL = {**{i: i for i in range(16)}, 0x10: 16, 0x11: 17, 0x12: 18,
               0x14: 19, 0x15: 20, 0x16: 21, 0x17: 22}


def dispatch(cmd, p, out):
    """返回响应长度；<0 = 错误（文本在 out）。"""
    if cmd == S.BIN_PING:
        return out.write(b"jtag_serve_bin v1-mock")
    if cmd == S.BIN_CMD:
        line = p.decode(errors="replace").strip()
        if line == "haltinfo":
            return out.write((b"state=halted reason=bkpt pc=0x%08X\n"
                              % TG.pc) if TG.halted else b"state=running\n")
        return out.write("ERR: mock 未知命令\n".encode())
    if cmd == S.BIN_HALTINFO:
        reason = 2 if TG.halted else 0
        return out.write(bytes([1 if TG.halted else 0, reason])
                          + struct.pack("<I", TG.pc if TG.halted else 0))
    if cmd == S.BIN_HALT:
        TG.halted = True
        return out.write(struct.pack("<I", TG.pc))
    if cmd == S.BIN_RESUME:
        TG.halted = False
        return 0
    if cmd == S.BIN_STEP:
        n = p[0] if p else 1
        TG.halted = True
        TG.pc += 2 * n
        return out.write(struct.pack("<I", TG.pc))
    if cmd == S.BIN_REG_RD:
        if not TG.halted:
            return out.err("target is running")
        for sel in p:
            out.write(struct.pack("<I", TG.regs[REGS_BY_SEL[sel]]))
        return len(p) * 4
    if cmd == S.BIN_REG_WR:
        sel = REGS_BY_SEL[p[0]]
        val = struct.unpack_from("<I", p, 1)[0]
        if sel == 15:
            TG.pc = val
        else:
            TG.regs[sel] = val
        return 0
    if cmd == S.BIN_MEM_RD:
        addr, w, cnt = struct.unpack("<IBH", p[:7])
        data = b""
        for k in range(cnt):
            data += (k * 8).to_bytes(w, "little")
        return out.write(data)
    if cmd == S.BIN_MEM_WR:
        addr, w, cnt = struct.unpack("<IBH", p[:7])
        return 0
    if cmd == S.BIN_BP_ADD:
        addr = struct.unpack("<I", p[:4])[0]
        TG.bps.append((addr, p[4] if p[4] in (2, 4) else 2))
        return out.write(bytes([len(TG.bps) - 1]))
    if cmd == S.BIN_BP_DEL:
        a = struct.unpack("<I", p[:4])[0]
        if a == 0xFFFFFFFF:
            n = len(TG.bps)
            TG.bps.clear()
            return out.write(bytes([n]))
        n = len([b for b in TG.bps if b[0] == a])
        TG.bps = [b for b in TG.bps if b[0] != a]
        return out.write(bytes([n]))
    if cmd == S.BIN_WP_ADD:
        addr, ln = struct.unpack("<II", p[:8])
        TG.wps.append((addr, ln, p[8]))
        return out.write(bytes([len(TG.wps) - 1]))
    if cmd == S.BIN_WP_DEL:
        a = struct.unpack("<I", p[:4])[0]
        if a == 0xFFFFFFFF:
            n = len(TG.wps)
            TG.wps.clear()
            return out.write(bytes([n]))
        n = len([w for w in TG.wps if w[0] == a])
        TG.wps = [w for w in TG.wps if w[0] != a]
        return out.write(bytes([n]))
    if cmd == S.BIN_BPS:
        out.write(bytes([len(TG.bps)]))
        for a, ln in TG.bps:
            out.write(struct.pack("<IB", a, ln))
        out.write(bytes([len(TG.wps)]))
        for a, ln, acc in TG.wps:
            out.write(struct.pack("<IIB", a, ln, acc))
        return len(out.buf)
    if cmd == S.BIN_SWO_TPIU:
        tclk, baud = struct.unpack("<II", p[:8])
        return out.write(struct.pack("<I", 4032258))
    if cmd == S.BIN_SWO_STAT:
        return out.write(bytes([0, 0, 0, 0]))
    if cmd == S.BIN_VREF:
        return out.write(struct.pack("<I", 3301))   # 3.301 V
    return out.err(f"unknown cmd 0x{cmd:02X}")


class Out:
    def __init__(self):
        self.buf = bytearray()

    def write(self, b):
        self.buf += b
        return len(self.buf)

    def err(self, msg):
        self.buf = msg.encode()
        return -1


async def bin_server(reader, writer):
    try:
        while True:
            hdr = await reader.readexactly(4)
            seq, cmd = hdr[0], hdr[1]
            plen = hdr[2] | (hdr[3] << 8)
            payload = await reader.readexactly(plen) if plen else b""
            out = Out()
            rc = dispatch(cmd, payload, out)
            body = bytes(out.buf)
            rcmd = S.BIN_ERR if rc < 0 else (cmd | 0x80)
            writer.write(bytes((seq, rcmd, len(body) & 0xFF,
                                len(body) >> 8)) + body)
            await writer.drain()
    except (ConnectionError, asyncio.IncompleteReadError):
        pass
    finally:
        writer.close()


async def swo_server(reader, writer):
    def ev(t, a):
        return bytes([(2 << 3) | 1, t, (2 << 3) | 3]) + \
               a.to_bytes(4, "little")

    def txt(s):
        return b"".join(bytes([(0 << 3) | 1, ord(c)]) for c in s)

    try:
        n = 0
        while True:
            n += 1
            writer.write(txt(f"hi{n} ") + ev(1, n) + bytes([0xC0, 7]))
            await writer.drain()
            await asyncio.sleep(0.02)
    except (ConnectionError, asyncio.IncompleteReadError):
        pass
    finally:
        writer.close()


async def main():
    cs = await asyncio.start_server(bin_server, "127.0.0.1", CMD_PORT)
    ss = await asyncio.start_server(swo_server, "127.0.0.1", SWO_PORT_M)
    S.OCD_PORT = CMD_PORT
    S.SWO_PORT = SWO_PORT_M
    S.board_addr = lambda host=None: "127.0.0.1"

    ok = True

    def check(name, cond, detail=""):
        nonlocal ok
        print(f"{'PASS' if cond else 'FAIL'}  {name} {detail}")
        ok = ok and cond

    # 1) haltinfo / tgt_probe
    state, reason, pc = await S.OCD.haltinfo()
    check("haltinfo running", state == "running")
    await S.OCD.halt()
    state, reason, pc = await S.OCD.haltinfo()
    check("haltinfo halted", state == "halted" and reason == "breakpoint"
          and pc == TG.pc)
    await S.tgt_probe()
    check("tgt_probe", S.ST.tgt_state == "halted"
          and S.ST.halt_reason == "breakpoint")

    # 2) regs 一次包
    regs = await S.OCD.regs()
    check("regs 23 个", len(regs) == 23 and regs["pc"] == TG.pc
          and regs["r0"] == 0, str(len(regs)))

    # 3) mem
    vals = await S.OCD.mem_read(0x20000000, 4, 4)
    check("mem_read", len(vals) == 4 and vals[0] == 0, repr(vals[:2]))
    await S.OCD.mem_write(0x20000800, 0xDEADBEEF, 4)

    # 4) step
    pc1 = TG.pc
    pc2 = await S.OCD.step(4)
    check("step ×4", pc2 == pc1 + 8, hex(pc2))

    # 5) bp/wp
    await S.OCD.bp_add(0x080002A8)
    await S.OCD.bp_add(0x08000000, 4)
    await S.OCD.wp_add(0x20000004, 4, "w")
    bps, wps = await S.OCD.bps()
    check("bps/wps", len(bps) == 2 and bps[1][1] == 4
          and len(wps) == 1 and wps[0][2] == "w")
    await S.OCD.bp_del(0x080002A8)
    bps, wps = await S.OCD.bps()
    check("bp_del 单个", len(bps) == 1)
    await S.OCD.bp_del()
    await S.OCD.wp_del()
    bps, wps = await S.OCD.bps()
    check("bp/wp all 清", not bps and not wps)

    # 6) swo_tpiu / cmd 文本 / 错误透出
    actual = await S.OCD.swo_tpiu(72000000, 4000000)
    check("swo_tpiu", actual == 4032258)
    out = await S.OCD.cmd("haltinfo")
    check("cmd 文本", "state=" in out)
    out = await S.OCD.cmd("nosuchcmd")
    check("cmd 未知命令文本", "未知" in out)
    try:
        await S.OCD._xchg(0x7E)          # 协议级未知命令 -> BIN_ERR
        check("BIN_ERR 抛错", False)
    except RuntimeError as e:
        check("BIN_ERR 抛错", "unknown" in str(e) or "0x7E" in str(e))

    # 7) resume + SWO 流解析
    await S.OCD.resume()
    swo_t = asyncio.create_task(S.swo_loop())
    await asyncio.sleep(1.2)
    check("SWO 文本", "hi" in "".join(S.ST.text)[-200:])
    check("SWO 事件", len(S.ST.events) > 5, str(len(S.ST.events)))
    swo_t.cancel()

    # 8) 断链重连
    await S.OCD._drop()
    state, _, _ = await S.OCD.haltinfo()
    check("断链重连", state in ("running", "halted"))

    cs.close(), ss.close()
    print("RESULT:", "ALL PASS" if ok else "HAS FAILURES")
    sys.exit(0 if ok else 1)


asyncio.run(main())
