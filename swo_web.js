#!/usr/bin/env node
/**
 * swo_web.js — SWO/调试 Web 控制台（Node.js 版，ITM 解析器 V8 JIT 加速）
 *
 * 架构与 Python 版（swo_web.py）完全兼容：
 *   - HTTP :8080 出单页 UI（ui.html，与 Python 版共用）
 *   - WebSocket /ws 实时推送（50ms 节奏，协议同 Python 版）
 *   - 命令口 5555 二进制帧协议 连 板上 jtag_tool --serve
 *   - SWO 流口 5556 原始字节 → ItmParser（TypedArray 批量解析）
 *   - REST API 端点与 Python 版路径/格式一致
 *
 * 用法:  node swo_web.js [board_host] [port] [elf_path]
 *        board_host 默认 elink.local；port 默认 8080
 *
 * 零依赖（Node.js ≥ 18 标准库）
 */

"use strict";

const net = require("net");
const http = require("http");
const crypto = require("crypto");
const fs = require("fs");
const path = require("path");
const { execFile } = require("child_process");

// ============================================================ 配置
const BOARD_HOST = process.argv[2] || "elink.local";
const PORT = parseInt(process.argv[3]) || 8080;
const OCD_PORT = 5555;
const SWO_PORT = 5556;
const SWO_PINFREQ = 8000000;
const GTC_HZ = 72000000;
const DWT_CTRL_ADDR = 0xE0001000;
const PCSAMPLENA = 1 << 12, EXCTRCENA = 1 << 16, CYCCNTENA = 1 << 0;

const ELF_CANDIDATES = [
    path.join(__dirname, "..", "swotest", "swotest.elf"),
    "/root/swotest.elf",
];
let ELF_PATH = ELF_CANDIDATES.find(p => fs.existsSync(p)) || ELF_CANDIDATES[0];
if (process.argv[4]) ELF_PATH = process.argv[4];

// ============================================================ 状态
const ST = {
    t0: Date.now(),
    text: [],           // 控制台文本
    pc_hist: new Map(), // PC → count
    pc_total: 0, pc_sleep: 0, pc_t0: Date.now(),
    exc: new Map(),     // exc → {n, h_sum, h_n, h_max, t_sum, t_n, p_sum, p_n}
    exc_events: 0, exc_recent: [], exc_mispaired: 0,
    resyncs: 0, overflows: 0, gtc: 0,
    mhz: 0, exc_ps: 0, sleep_pct: 0, dwt_raw: [0,0,0,0,0,0],
    pc_on: false, exc_on: false,
    ocd_ok: false, swo_ok: false,
    swo_traceclk: 72000000, swo_baud: SWO_PINFREQ,
    swo_state: "init", swo_conn_n: 0, swo_last_err: "",
    tgt_state: "unknown", halt_reason: "", halt_pc: null,
    regs: {}, bps: [], wps: [],
    watches: [], watch_ms: 50,
    chan_text: new Map(), event_port: 2,
    evt_desync: 0, stamp_drops: 0, events: [], _awaiting: [], evt_state: 0, evt_type: 0, last_exit: null, last_ret: null, r_sum: 0, r_n: 0,
    syms: [], objs: [], sym_by_name: new Map(),
    disasm: null, disasmSrc: null,
    elf_path: ELF_PATH,
};

// ============================================================ ELF 符号表
function loadSymbols(elfPath) {
    try {
        const data = fs.readFileSync(elfPath);
        if (data.slice(0, 4).toString() !== "\x7fELF") return;
        const is64 = data[4] === 2;
        let shoff, shentsize, shnum;
        if (is64) {
            shoff = data.readBigUInt64LE(0x28);
            shentsize = data.readUInt16LE(0x3A); shnum = data.readUInt16LE(0x3C);
        } else {
            shoff = data.readUInt32LE(0x20);
            shentsize = data.readUInt16LE(0x2E); shnum = data.readUInt16LE(0x30);
        }
        const shs = [];
        for (let i = 0; i < shnum; i++) {
            const o = Number(shoff) + i * shentsize;
            if (is64) {
                shs.push({
                    type: data.readUInt32LE(o + 4),
                    addr: Number(data.readBigUInt64LE(o + 16)),
                    offset: Number(data.readBigUInt64LE(o + 24)),
                    size: Number(data.readBigUInt64LE(o + 32)),
                    link: data.readUInt32LE(o + 40),
                    entsize: Number(data.readBigUInt64LE(o + 56)),
                });
            } else {
                shs.push({
                    type: data.readUInt32LE(o + 4),
                    addr: data.readUInt32LE(o + 12),
                    offset: data.readUInt32LE(o + 16),
                    size: data.readUInt32LE(o + 20),
                    link: data.readUInt32LE(o + 24),
                    entsize: data.readUInt32LE(o + 36),
                });
            }
        }
        let symtab = null, strtab = null;
        for (const sh of shs) {
            if (sh.type === 2) { symtab = sh; strtab = shs[sh.link]; break; }
        }
        if (!symtab || !strtab) return;
        const str = data.slice(strtab.offset, strtab.offset + strtab.size);
        const funcs = [], objs = [], byName = new Map();
        // Elf32_Sym=16B / Elf64_Sym=24B；section 的 entsize 字段本身就是它
        const entsize = (is64 ? 24 : 16);
        const n = Math.floor(symtab.size / entsize);
        for (let i = 0; i < n; i++) {
            const o = symtab.offset + i * entsize;
            let nameOff, val, sz, info;
            if (is64) {
                nameOff = Number(data.readBigUInt64LE(o));
                val = Number(data.readBigUInt64LE(o + 8));
                sz = Number(data.readBigUInt64LE(o + 16));
                info = data.readUInt8(o + 4);
            } else {
                nameOff = data.readUInt32LE(o);
                val = data.readUInt32LE(o + 4);
                sz = data.readUInt32LE(o + 8);
                info = data.readUInt8(o + 12);
            }
            const typ = info & 0xF;
            if (typ !== 1 && typ !== 2) continue;
            if (sz === 0 || val === 0) continue;
            const end = str.indexOf(0, nameOff);
            const name = str.slice(nameOff, end).toString();
            if (!name || name.startsWith("$")) continue;
            if (typ === 2) val &= 0xFFFFFFFE;  // Thumb bit
            (typ === 2 ? funcs : objs).push([val, sz, name]);
            if (!byName.has(name)) byName.set(name, [val, sz]);
        }
        funcs.sort((a, b) => a[0] - b[0]);
        objs.sort((a, b) => a[0] - b[0]);
        ST.syms = funcs; ST.objs = objs; ST.sym_by_name = byName;
        console.log(`swo_web: ELF ${path.basename(elfPath)}: ${funcs.length} funcs + ${objs.length} objs`);
    } catch (e) {
        console.error(`ELF load failed: ${e.message}`);
    }
}

// ============================================================ jtag_tool 二进制客户端
const BIN = {
    PING:1, CMD:2, HALTINFO:3, HALT:4, RESUME:5, STEP:6,
    REG_RD:7, REG_WR:8, MEM_RD:9, MEM_WR:0xA,
    BP_ADD:0xB, BP_DEL:0xC, WP_ADD:0xD, WP_DEL:0xE, BPS:0xF,
    SWO_TPIU:0x10, SWO_STAT:0x11, REPROBE:0x12, ERR:0x7F,
};
const REG_NAMES = ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12",
                   "sp","lr","pc","xpsr","msp","psp","primask","basepri","faultmask","control"];
const REG_SELS = Buffer.from([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,22,23]);

class Ocd {
    constructor() {
        this.sock = null; this.seq = 0;
        this.pending = new Map();
        this.eioStreak = 0;
    }
    connect() {
        return new Promise((resolve, reject) => {
            const sock = net.connect(OCD_PORT, ST._boardIp, () => {
                this.sock = sock;
                ST.ocd_ok = true;
                this.xchg(BIN.SWO_TPIU, this.packII(ST.swo_traceclk, ST.swo_baud))
                    .then(() => this.setTrace()).catch(() => {});
                resolve();
            });
            sock.on("error", (e) => { ST.ocd_ok = false; this.sock = null; reject(e); });
            sock.on("close", () => { ST.ocd_ok = false; this.sock = null; });
            sock.on("data", (data) => this._onData(data));
            this._buf = Buffer.alloc(0);
        });
    }
    packII(a, b) { const p = Buffer.alloc(8); p.writeUInt32LE(a, 0); p.writeUInt32LE(b, 4); return p; }
    packIBH(a, b, c) { const p = Buffer.alloc(7); p.writeUInt32LE(a, 0); p.writeUInt8(b, 4); p.writeUInt16LE(c, 5); return p; }
    _onData(data) {
        this._buf = Buffer.concat([this._buf, data]);
        while (this._buf.length >= 4) {
            const seq = this._buf[0], cmd = this._buf[1];
            const len = this._buf[2] | (this._buf[3] << 8);
            if (this._buf.length < 4 + len) break;
            const body = this._buf.slice(4, 4 + len);
            this._buf = this._buf.slice(4 + len);
            const cb = this.pending.get(seq);
            if (cb) { this.pending.delete(seq); cb(cmd, body); }
        }
    }
    xchg(cmd, payload = Buffer.alloc(0), timeout = 8000) {
        return new Promise((resolve, reject) => {
            if (!this.sock) { reject(new Error("no connection")); return; }
            this.seq = (this.seq + 1) & 0xFF;
            const hdr = Buffer.alloc(4);
            hdr[0] = this.seq; hdr[1] = cmd;
            hdr.writeUInt16LE(payload.length, 2);
            const timer = setTimeout(() => {
                this.pending.delete(this.seq);
                reject(new Error("timeout"));
            }, timeout);
            this.pending.set(this.seq, (rc, body) => {
                clearTimeout(timer);
                if (rc === BIN.ERR) {
                    reject(new Error(body.toString()));
                } else {
                    this.eioStreak = 0;
                    resolve(body);
                }
            });
            this.sock.write(Buffer.concat([hdr, payload]));
        });
    }
    async cmd(line, timeout = 8000) {
        const b = await this.xchg(BIN.CMD, Buffer.from(line.slice(0, 200)), timeout);
        return b.toString();
    }
    async haltinfo() {
        const b = await this.xchg(BIN.HALTINFO);
        return { state: b[0] ? "halted" : "running",
                 reason: ["","debug-request","breakpoint","watchpoint","vector-catch","external"][b[1]] || "",
                 pc: b.length >= 6 ? b.readUInt32LE(2) : null };
    }
    async halt() { const b = await this.xchg(BIN.HALT); return b.length === 4 ? b.readUInt32LE(0) : null; }
    async resume() { await this.xchg(BIN.RESUME); }
    async step(n = 1) {
        const b = await this.xchg(BIN.STEP, Buffer.from([Math.max(1, Math.min(16, n))]), 20000);
        return b.length === 4 ? b.readUInt32LE(0) : null;
    }
    async regs() {
        const b = await this.xchg(BIN.REG_RD, REG_SELS);
        const out = {};
        for (let i = 0; i < REG_NAMES.length && i * 4 + 4 <= b.length; i++) {
            out[REG_NAMES[i]] = b.readUInt32LE(i * 4);
        }
        return out;
    }
    async memRead(addr, count, width = 4) {
        const b = await this.xchg(BIN.MEM_RD, this.packIBH(addr, width, Math.min(1024, count)));
        const per = width, vals = [];
        for (let i = 0; i * per + per <= b.length; i++) {
            vals.push(b.readUIntLE(i * per, per));
        }
        return vals.slice(0, count);
    }
    async memWrite(addr, val, width = 4) {
        const payload = Buffer.concat([this.packIBH(addr, width, 1),
            (() => { const b = Buffer.alloc(width); b.writeUIntLE(val, 0, width); return b; })()]);
        await this.xchg(BIN.MEM_WR, payload);
    }
    async bpAdd(addr, len = 2) {
        const p = Buffer.alloc(5); p.writeUInt32LE(addr, 0); p[4] = len;
        await this.xchg(BIN.BP_ADD, p);
    }
    async bpDel(addr = null) {
        const p = Buffer.alloc(4); p.writeUInt32LE(addr === null ? 0xFFFFFFFF : addr, 0);
        await this.xchg(BIN.BP_DEL, p);
    }
    async wpAdd(addr, len, acc) {
        const p = Buffer.alloc(9); p.writeUInt32LE(addr, 0); p.writeUInt32LE(len, 4);
        p[8] = { r: 5, w: 6, a: 7 }[acc] || 6;
        await this.xchg(BIN.WP_ADD, p);
    }
    async wpDel(addr = null) {
        const p = Buffer.alloc(4); p.writeUInt32LE(addr === null ? 0xFFFFFFFF : addr, 0);
        await this.xchg(BIN.WP_DEL, p);
    }
    async bps() {
        const b = await this.xchg(BIN.BPS);
        const bps = [], wps = [];
        let i = 0, nb = b[i++];
        for (let k = 0; k < nb; k++) { bps.push([b.readUInt32LE(i), b[i+4]]); i += 5; }
        let nw = b[i++];
        for (let k = 0; k < nw; k++) { wps.push([b.readUInt32LE(i), b.readUInt32LE(i+4), b[i+8]]); i += 9; }
        return { bps, wps };
    }
    async swoTpiu(traceclk, baud) {
        const b = await this.xchg(BIN.SWO_TPIU, this.packII(traceclk, baud));
        this.setTrace().catch(() => {});
        return b.length === 4 ? b.readUInt32LE(0) : 0;
    }
    async swoStat() {
        const b = await this.xchg(BIN.SWO_STAT);
        return { cnt: b[0] | (b[1] << 8), ovr: b[2], fe: b[3] };
    }
    async setTrace(pc = null, exc = null) {
        if (pc !== null) ST.pc_on = pc;
        if (exc !== null) ST.exc_on = exc;
        let v = CYCCNTENA;
        if (ST.pc_on) v |= PCSAMPLENA;
        if (ST.exc_on) v |= EXCTRCENA;
        await this.memWrite(DWT_CTRL_ADDR, v);
        return v;
    }
}
const OCD = new Ocd();

// ============================================================ ITM 解析器（V8 JIT 核心）
const SIZE_LUT = [null, 1, 2, 4];  // 长度码 0 无效（Python SIZE 无 key 0），3=4B
class ItmParser {
    // Python ItmParser 逐行移植（_parse/_stamp/_resync/feed）
    // ANCHORS: 重同步锚点（已知包头字节，与 Python 版一致）
    static ANCHORS = [0x0E, 0x17, 0x15, 0x01, 0xC0];
    // ITM 长度码：{1:1, 2:2, 3:4}——0 无效（Python SIZE 无 key 0）
    static SIZE = { 1: 1, 2: 2, 3: 4 };

    constructor() {
        this.buf = Buffer.alloc(0);
    }

    feed(data) {
        this.buf = this.buf.length === 0 ? data : Buffer.concat([this.buf, data]);
        const i = this.parse();
        this.buf = this.buf.slice(i);
    }

    _resync(i) {
        ST.resyncs++;
        const buf = this.buf, n = buf.length;
        let best = n;
        for (const pat of ItmParser.ANCHORS) {
            // 找最近的锚点（与 Python bytes.find 语义一致）
            for (let j = i + 1; j < Math.min(n, i + 256); j++) {
                if (buf[j] === pat) { if (j < best) best = j; break; }
            }
        }
        return best;
    }

    _stamp(gtc) {
        /* ts 到达：给它前面最近的未配时项定时（异常或 ITM 事件） */
        if (!ST._awaiting || ST._awaiting.length === 0) return;
        if (ST._awaiting.length > 1) ST.stamp_drops += ST._awaiting.length - 1;
        const item = ST._awaiting.pop(); // [src, kind/type, exc/arg]
        if (item[0] === "evt") {
            ST.events.push({ gtc, type: item[1], arg: item[2] });
            if (ST.events.length > 2000) ST.events.shift();
            return;
        }
        const kind = item[1], exc = item[2];
        ST.exc_recent.push({ gtc, k: kind, exc });
        if (ST.exc_recent.length > 40) ST.exc_recent.shift();

        if (kind === "ret") {
            if (ST.last_exit !== null) { ST.r_sum += gtc - ST.last_exit; ST.r_n++; }
            ST.last_ret = gtc;
            return;
        }
        if (exc > 63) { ST.exc_mispaired++; return; }
        let d = ST.exc.get(exc);
        if (kind === "entry") {
            if (!d) {
                d = { n:0, h_sum:0, h_n:0, h_max:0, t_sum:0, t_n:0,
                      p_sum:0, p_n:0, last_entry:null, p_est:null };
                ST.exc.set(exc, d);
            }
            // n 已在 parse 侧计数
            if (d.last_entry !== null) {
                const p = gtc - d.last_entry;
                d.p_sum += p; d.p_n++;
                if (p > 0 && p < (1 << 31)) d.p_est = p;
            }
            if (ST.last_ret !== null) { d.t_sum += gtc - ST.last_ret; d.t_n++; }
            d.last_entry = gtc;
        } else if (kind === "exit") {
            if (d && d.last_entry !== null) {
                const h = gtc - d.last_entry;
                const thr = d.p_est ? Math.floor(d.p_est / 4) : 2000000;
                if (h >= 0 && h < thr) {
                    d.h_sum += h; d.h_n++;
                    if (h > d.h_max) d.h_max = h;
                } else {
                    ST.exc_mispaired++;
                }
            }
            ST.last_exit = gtc;
        }
    }

    parse() {
        const buf = this.buf, n = buf.length;
        const SIZE = ItmParser.SIZE;
        let i = 0;

        while (i < n) {
            const c = buf[i];

            // ---- 快路径：PC 采样（0x17/0x15，占流量 95%）----
            if (c === 0x17 || c === 0x15) {
                if (c === 0x15) { ST.pc_sleep++; i += 1; continue; }
                if (i + 5 <= n) {
                    ST.pc_total++;
                    const pc = buf[i+1] | (buf[i+2] << 8) | (buf[i+3] << 16) | (buf[i+4] << 24);
                    if (!(pc & 1)) ST.pc_hist.set(pc, (ST.pc_hist.get(pc) || 0) + 1);
                    i += 5;
                    continue;
                }
                // 不完整（缓冲尾）→ 走慢路径等下一批
            }

            // ---- 时间戳：0xC0-0xFF & low nibble 0，payload 7bit 累加 ----
            if ((c & 0x0F) === 0 && c >= 0xC0) {
                let j = i + 1, val = 0, shift = 0, done = false;
                while (j < n && j - i <= 5) {
                    const b = buf[j];
                    val |= (b & 0x7F) << shift; shift += 7; j++;
                    if (!(b & 0x80)) { done = true; break; }
                }
                if (done) {
                    ST.gtc += val;
                    this._stamp(ST.gtc);
                    i = j;
                } else if (j >= n) {
                    return i;  // 缓冲不足
                } else {
                    i = this._resync(i);
                }
                continue;
            }

            if (c === 0x70) { ST.overflows++; i += 1; continue; }

            if (c === 0x00 || (c & 0x0F) === 0x04 || (c & 0x0F) === 0x08 || (c & 0x0F) === 0x0C) {
                ST.resyncs++;
                i = (c === 0x00) ? this._resync(i) : i + 1;
                continue;
            }

            const size = SIZE[c & 3];
            if (size === undefined) { i = this._resync(i); continue; }
            if (i + 1 + size > n) return i;  // 包不完整

            const payload = buf.slice(i + 1, i + 1 + size);

            if (c & 0x04) {  // ---- DWT 硬件源 ----
                const typ = c >> 3;
                if (typ === 2 && size === 4) {  // PC 采样（慢路径）
                    const pc = payload.readUInt32LE(0);
                    ST.pc_hist.set(pc, (ST.pc_hist.get(pc) || 0) + 1);
                    ST.pc_total++;
                } else if (typ === 1 && size === 2) {  // 异常跟踪
                    const v = payload.readUInt16LE(0);
                    const kind = { 1: "entry", 2: "exit", 3: "ret" }[v >> 12] || null;
                    if (kind) {
                        ST.exc_events++;
                        ST._awaiting.push(["exc", kind, v & 0x1FF]);
                        if (kind === "entry" || kind === "exit") {
                            const excN = v & 0x1FF;
                            if (excN > 1) {
                                let d = ST.exc.get(excN);
                                if (!d) {
                                    d = { n:0, n_exit:0, h_sum:0, h_n:0, h_max:0,
                                          t_sum:0, t_n:0, p_sum:0, p_n:0,
                                          last_entry:null, p_est:null };
                                    ST.exc.set(excN, d);
                                }
                                if (kind === "entry") d.n++;
                                else { d.n_exit++; if (d.n < d.n_exit) d.n = d.n_exit; }
                            }
                        }
                    }
                }
            } else if ((c >> 3) === 0) {  // ---- SWIT port0 文本 ----
                const s = payload.toString("ascii");
                let ok = true;
                for (const ch of s) {
                    if (ch.charCodeAt(0) < 32 && !"\r\n\t".includes(ch)) { ok = false; break; }
                }
                if (ok) {
                    for (const ch of s) ST.text.push(ch);
                    if (ST.text.length > 40000) ST.text.splice(0, ST.text.length - 40000);
                }
            } else {  // ---- 其余 stimulus port（1-31）----
                const port = c >> 3;
                if (port === ST.event_port) {
                    // 事件协议：1B type + 4B arg
                    if (ST.evt_state === 0) {
                        if (size === 1 && payload[0] < 64) {
                            ST.evt_type = payload[0];
                            ST.evt_state = 1;
                        } else {
                            ST.evt_desync++;
                        }
                    } else if (size === 4) {
                        ST._awaiting.push(["evt", ST.evt_type, payload.readUInt32LE(0)]);
                        ST.evt_state = 0;
                    } else if (size === 1 && payload[0] < 64) {
                        ST.evt_desync++;
                        ST.evt_type = payload[0];
                    } else {
                        ST.evt_desync++;
                        ST.evt_state = 0;
                    }
                } else {
                    // 通道文本
                    const s = payload.toString("ascii");
                    let ok = true;
                    for (const ch of s) {
                        if (ch.charCodeAt(0) < 32 && !"\r\n\t".includes(ch)) { ok = false; break; }
                    }
                    if (ok) {
                        let txt = ST.chan_text.get(port);
                        if (!txt) { txt = []; ST.chan_text.set(port, txt); }
                        for (const ch of s) txt.push(ch);
                        if (txt.length > 20000) txt.splice(0, txt.length - 20000);
                    }
                }
            }
            i += 1 + size;
        }
        return i;
    }
}

const PARSER = new ItmParser();

// ============================================================ 板地址解析
function resolveBoard() {
    return new Promise((resolve) => {
        const { execFile } = require("child_process");
        execFile("avahi-resolve", ["-4", "-n", BOARD_HOST], { timeout: 3000 }, (err, stdout) => {
            if (!err && stdout) {
                const parts = stdout.trim().split(/\s+/);
                if (parts.length >= 2) { resolve(parts[1]); return; }
            }
            // fallback: direct IP or DNS
            require("dns").lookup(BOARD_HOST, (err2, addr) => {
                resolve(err2 ? BOARD_HOST : addr);
            });
        });
    });
}

// ============================================================ SWO 流客户端
async function swoLoop() {
    /* 静默看门狗：DWT 在产流却 10s 零字节 = 目标复位后 SWO 输出停了
       （寄存器全被清），swo_tpiu 重配（内含 SWJ_CFG 循环）+ setTrace
       重放 DWT_CTRL 一脚踢活。与 Python 版语义一致。 */
    setInterval(async () => {
        if (!ST.swo_ok || !ST.swo_last_rx) return;
        const silent = (Date.now() - ST.swo_last_rx) / 1000;
        if (silent > 10 && (ST.pc_on || ST.exc_on)) {
            ST.swo_state = "静默>" + silent.toFixed(0) + "s，重配踢活中";
            try { await OCD.swoTpiu(ST.swo_traceclk, ST.swo_baud); } catch (e) {}
            ST.swo_state = "reading";
        }
    }, 5000).unref();

    while (true) {
        try {
            const ip = await resolveBoard();
            ST._boardIp = ip;
            ST.swo_state = `connecting (${++ST.swo_conn_n})`;
            await new Promise((resolve, reject) => {
                const sock = net.connect(SWO_PORT, ip, () => {
                    ST.swo_ok = true; ST.swo_state = "reading";
                    ST.swo_last_rx = Date.now();
                    resolve();
                });
                sock.on("error", reject);
                sock.on("close", () => { ST.swo_ok = false; reject(new Error("closed")); });
                sock.on("data", (data) => {
                    ST.swo_last_rx = Date.now();
                    PARSER.feed(data);
                });
                ST._swoSock = sock;
            });
            // 连接成功后等断开
            await new Promise((resolve) => {
                if (ST._swoSock) ST._swoSock.on("close", resolve);
                else resolve();
            });
        } catch (e) {
            ST.swo_last_err = e.message;
        }
        ST.swo_ok = false; ST.swo_state = "对端关闭，重连中";
        await new Promise(r => setTimeout(r, 1000));
    }
}

// ============================================================ 后台循环
async function withRetry(fn, interval) {
    while (true) {
        try { await fn(); } catch (e) { /* silent */ }
        await new Promise(r => setTimeout(r, interval));
    }
}

async function tgtLoop() {
    if (!OCD.sock) { await OCD.connect().catch(() => {}); return; }
    const info = await OCD.haltinfo();
    ST.tgt_state = info.state; ST.halt_reason = info.reason; ST.halt_pc = info.pc;
    if (info.state === "halted") {
        const regs = await OCD.regs();
        if (regs && Object.keys(regs).length) ST.regs = regs;
    } else {
        ST.regs = {};
    }
}

let dwtPrev = null;
async function dwtLoop() {
    if (!OCD.sock) return;
    const vals = await OCD.memRead(0xE0001004, 6);
    if (vals && vals.length === 6) {
        ST.dwt_raw = vals;
        const now = Date.now();
        if (dwtPrev) {
            const dt = Math.max(now - dwtPrev.t, 1) / 1000;
            const dcyc = ((vals[0] - dwtPrev.v[0]) >>> 0);
            ST.mhz = dcyc < 0x8000000 ? dcyc / dt / 1e6 : 0;
            ST.exc_ps = ((vals[2] - dwtPrev.v[2]) & 0xFF) / dt;
            const dslp = ((vals[3] - dwtPrev.v[3]) & 0xFF);
            ST.sleep_pct = dcyc ? Math.min(dslp * 100 / dcyc, 100) : 100;
        }
        dwtPrev = { v: vals, t: now };
    }
}

async function watchLoop() {
    if (!ST.watches.length || ST.tgt_state === "unknown" || !OCD.sock) return;
    const ws = [...ST.watches].sort((a, b) => a.addr - b.addr);
    const segs = [];
    for (const w of ws) {
        const b = w.addr & ~3;
        if (segs.length && b < segs[segs.length-1][0] + segs[segs.length-1][1] * 4 + 64) {
            const need = Math.ceil((b + 4 - segs[segs.length-1][0]) / 4);
            if (need > segs[segs.length-1][1]) segs[segs.length-1][1] = need;
        } else {
            segs.push([b, 1]);
        }
    }
    const words = new Map();
    for (const [base, cnt] of segs) {
        try {
            const vals = await OCD.memRead(base, cnt);
            if (vals) vals.forEach((v, k) => words.set(base + 4 * k, v));
        } catch (e) { /* skip */ }
    }
    const now = Date.now() / 1000;
    for (const w of ST.watches) {
        let word = words.get(w.addr & ~3);
        if (word !== undefined && w.size < 4) {
            word = (word >> ((w.addr & 3) * 8)) & ((1 << (w.size * 8)) - 1);
        }
        w.series.push([now, word]);
        if (w.series.length > 600) w.series.shift();
        w.n = (w.n || 0) + 1;
    }
}

// ============================================================ REST API
function json(res, obj, status = 200) {
    const body = JSON.stringify(obj);
    res.writeHead(status, { "Content-Type": "application/json; charset=utf-8",
        "Content-Length": Buffer.byteLength(body), "Cache-Control": "no-store" });
    res.end(body);
}

async function readBody(req) {
    return new Promise((resolve) => {
        let data = "";
        req.on("data", (c) => data += c);
        req.on("end", () => { try { resolve(JSON.parse(data || "{}")); } catch { resolve({}); } });
    });
}

function apiStatus() {
    return {
        uptime_s: Math.round((Date.now() - ST.t0) / 1000) / 1,
        ocd: ST.ocd_ok, swo: ST.swo_ok,
        mhz: Math.round(ST.mhz * 100) / 100, gtc_hz: GTC_HZ,
        pc_on: ST.pc_on, exc_on: ST.exc_on,
        pc_total: ST.pc_total, pc_sleep: ST.pc_sleep,
        exc_events: ST.exc_events,
        resyncs: ST.resyncs, overflows: ST.overflows,
        tgt_state: ST.tgt_state, halt_reason: ST.halt_reason,
        halt_pc: ST.halt_pc !== null ? "0x" + ST.halt_pc.toString(16).padStart(8, "0") : null,
        backend: "nodejs",
        swo_traceclk: ST.swo_traceclk, swo_baud: ST.swo_baud,
        swo_state: ST.swo_state, swo_conn_n: ST.swo_conn_n,
        chan_ports: [0, ...[...ST.chan_text.keys()].filter(p => ST.chan_text.get(p).length >= 16)].sort((a,b)=>a-b),
        event_port: ST.event_port,
        evt_desync: ST.evt_desync, evt_total: ST.events.length,
        elf: ST.elf_path, symbols: ST.syms.length, objects: ST.objs.length,
    };
}

function apiPcstats() {
    const elapsed = Math.max((Date.now() - ST.pc_t0) / 1000, 0.001);
    const top = [...ST.pc_hist.entries()].sort((a, b) => b[1] - a[1]).slice(0, 25);
    return {
        total: ST.pc_total, sleep: ST.pc_sleep,
        elapsed_s: Math.round(elapsed * 10) / 10,
        rate_per_s: Math.round(ST.pc_total / elapsed * 10) / 10,
        top: top.map(([addr, cnt]) => ({
            pc: "0x" + addr.toString(16).padStart(8, "0"),
            n: cnt, pct: Math.round(10000 * cnt / (ST.pc_total || 1)) / 100,
            sym: symLookup(addr),
        })),
    };
}

function symLookup(addr) {
    if (!ST.syms.length) return "0x" + addr.toString(16);
    let lo = 0, hi = ST.syms.length - 1, best = null;
    while (lo <= hi) {
        const mid = (lo + hi) >> 1;
        const [a, sz, name] = ST.syms[mid];
        if (a <= addr) { best = [a, name]; lo = mid + 1; }
        else hi = mid - 1;
    }
    /* 始终 name+offset（与 Python 版一致），恰好等于起始地址就不加 */
    if (best) {
        const off = addr - best[0];
        return off === 0 ? best[1] : `${best[1]}+0x${off.toString(16)}`;
    }
    return "0x" + addr.toString(16);
}

function apiExcstats() {
    const us = GTC_HZ / 1e6;
    const irqs = [];
    for (const [exc, d] of [...ST.exc.entries()].sort((a, b) => a[0] - b[0])) {
        if (!d.n) continue;
        irqs.push({
            exc, n: d.n,
            h_avg_us: d.h_n ? Math.round(d.h_sum / d.h_n / us * 1000) / 1000 : null,
            h_max_us: Math.round(d.h_max / us * 1000) / 1000,
            t_avg_us: d.t_n ? Math.round(d.t_sum / d.t_n / us * 10) / 10 : null,
            p_avg_us: d.p_n ? Math.round(d.p_sum / d.p_n / us * 10) / 10 : null,
        });
    }
    return {
        events: ST.exc_events, resyncs: ST.resyncs,
        mispaired: ST.exc_mispaired, irqs,
        recent: ST.exc_recent.slice(-30).map(e => ({
            ms: Math.round(e.gtc / (GTC_HZ / 1000) * 1000) / 1000,
            k: ["", "entry", "exit", "ret"][e.k] || e.k, exc: e.exc,
        })),
    };
}

function apiEvents() {
    const cutoffGtc = ST.gtc - 60 * GTC_HZ;
    const evs = ST.events.filter(e => e.gtc >= cutoffGtc).map(e => ({
        ms: Math.round(e.gtc / (GTC_HZ / 1000) * 1000) / 1000,
        src: "evt", type: e.type, arg: e.arg,
    }));
    for (const e of ST.exc_recent) {
        if (e.gtc >= cutoffGtc) {
            evs.push({ ms: Math.round(e.gtc / (GTC_HZ / 1000) * 1000) / 1000,
                       src: "exc", k: ["", "entry", "exit", "ret"][e.k] || e.k, exc: e.exc });
        }
    }
    evs.sort((a, b) => a.ms - b.ms);
    return { events: evs.slice(-300), desync: ST.evt_desync, stamp_drops: ST.stamp_drops };
}

// ============================================================ WebSocket
const wsSessions = new Set();

function wsHandshake(req, socket) {
    const key = req.headers["sec-websocket-key"];
    if (!key) { socket.destroy(); return; }
    const accept = crypto.createHash("sha1").update(key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").digest("base64");
    socket.write(`HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ${accept}\r\n\r\n`);
}

function wsEncode(text) {
    const payload = Buffer.from(text);
    const n = payload.length;
    let hdr;
    if (n < 126) hdr = Buffer.from([0x81, n]);
    else if (n < 65536) { hdr = Buffer.alloc(4); hdr[0] = 0x81; hdr[1] = 126; hdr.writeUInt16BE(n, 2); }
    else { hdr = Buffer.alloc(10); hdr[0] = 0x81; hdr[1] = 127; hdr.writeBigUInt64BE(BigInt(n), 2); }
    return Buffer.concat([hdr, payload]);
}

async function wsSession(req, socket) {
    wsHandshake(req, socket);
    const sess = { socket, tab: "console", conport: 0, queue: [], pending: new Map(), nextId: 1 };
    wsSessions.add(sess);
    let buf = Buffer.alloc(0);

    // 消息解析
    socket.on("data", (data) => {
        buf = Buffer.concat([buf, data]);
        while (buf.length >= 2) {
            const masked = !!(buf[1] & 0x80);
            const ln = buf[1] & 0x7F; let off = 2;
            if (ln === 126) { if (buf.length < 4) break; off = 4; }
            if (masked) off += 4;   // 跳过 4 字节掩码键
            const total = off + (ln === 126 ? buf.readUInt16BE(2) : ln);
            if (buf.length < total) break;
            let payload = buf.slice(off, total);
            if (masked) {            // RFC6455：客户端帧必须掩码，服务器 XOR 解码
                const msk = buf.slice(off - 4, off);
                payload = Buffer.from(payload);
                for (let i = 0; i < payload.length; i++)
                    payload[i] ^= msk[i & 3];
            }
            buf = buf.slice(total);
            try {
                const msg = JSON.parse(payload.toString());
                handleWsMessage(sess, msg).catch(() => {});
            } catch (e) { /* ignore */ }
        }
    });
    socket.on("close", () => wsSessions.delete(sess));
    socket.on("error", () => wsSessions.delete(sess));

    // 推送循环
    const pushTimer = setInterval(() => {
        if (socket.destroyed) { clearInterval(pushTimer); return; }
        try {
            const payload = { t: "push", status: apiStatus(), tab: sess.tab };
            if (sess.tab === "prof") payload.data = apiPcstats();
            else if (sess.tab === "exc") payload.data = apiExcstats();
            else if (sess.tab === "tl2") payload.data = apiEvents();
            else if (sess.tab === "debug") {
                payload.data = { state: ST.tgt_state, reason: ST.halt_reason,
                    pc: ST.halt_pc !== null ? "0x" + ST.halt_pc.toString(16).padStart(8, "0") : null,
                    regs: Object.fromEntries(Object.entries(ST.regs).map(([k, v]) => [k, "0x" + v.toString(16).padStart(8, "0")])) };
            } else if (sess.tab === "watch") {
                /* 增量推送（与 Python 版逐字节一致）：绝对计数游标，
                   只发新点；列表变更或回绕发全量+full 标记 */
                const ws = ST.watches;
                const sig = ws.map(w => `${w.name}|${w.fmt}|${w.win || 1}`).join(",");
                if (!sess.wcur) sess.wcur = { sig: null, sent: new Map() };
                const cur = sess.wcur;
                const full = cur.sig !== sig;
                if (full) { cur.sig = sig; cur.sent.clear(); }
                const watches = ws.map(w => {
                    const nAbs = w.n || w.series.length;
                    const sent = cur.sent.get(w.name) || 0;
                    const lag = nAbs - sent;
                    let pts, fullW;
                    if (full || lag > w.series.length || lag < 0) {
                        pts = w.series.map(([t, v]) => [Math.round(t * 1000) / 1000, v]);
                        fullW = true;
                    } else {
                        pts = lag > 0 ?
                            w.series.slice(-lag).map(([t, v]) => [Math.round(t * 1000) / 1000, v]) : [];
                        fullW = false;
                    }
                    cur.sent.set(w.name, nAbs);
                    return {
                        name: w.name,
                        addr: "0x" + w.addr.toString(16).padStart(8, "0"),
                        size: w.size, fmt: w.fmt, win: w.win || 1,
                        full: fullW, pts,
                    };
                });
                payload.data = { watches };
            } else if (sess.tab === "dwt") {
                payload.data = { mhz: Math.round(ST.mhz * 100) / 100,
                    exc_ps: Math.round(ST.exc_ps * 10) / 10,
                    sleep_pct: Math.round(ST.sleep_pct * 10) / 10,
                    raw: { cyc: "0x" + ST.dwt_raw[0].toString(16).padStart(8, "0"),
                           cpi: ST.dwt_raw[1], exc: ST.dwt_raw[2],
                           slp: ST.dwt_raw[3], lsu: ST.dwt_raw[4], fold: ST.dwt_raw[5] } };
            }
            socket.write(wsEncode(JSON.stringify(payload)));
            // 发送待回复的消息
            for (const [id, resp] of sess.pending) {
                const m = { t: "resp", id, ...resp };
                socket.write(wsEncode(JSON.stringify(m)));
            }
            sess.pending.clear();
        } catch (e) { /* ignore */ }
    }, 50);
}

async function handleWsMessage(sess, msg) {
    const t = msg.t || "";
    const id = msg.id;
    const reply = (obj) => { if (id !== undefined) sess.pending.set(id, obj); };

    try {
        if (t === "tab") sess.tab = String(msg.v || "console");
        else if (t === "conport") sess.conport = msg.v || 0;
        else if (t === "conback") {
            const buf = sess.conport === 0 ? ST.text : (ST.chan_text.get(sess.conport) || []);
            reply({ s: buf.slice(-6000).join("") });
        }
        else if (t === "cmd") reply({ out: (await OCD.cmd(String(msg.line || "").slice(0, 200))).slice(-2000) });
        else if (t === "action") {
            const a = msg.a || "";
            if (a === "halt") await OCD.halt();
            else if (a === "resume") await OCD.resume();
            else if (a === "reset") await OCD.memWrite(0xE000ED0C, 0x05FA0004);
            else if (a === "reset_halt") {
                await OCD.memWrite(0xE000ED0C, 0x05FA0004);
                const pc = await OCD.halt();
                reply({ out: `halted pc=0x${(pc || 0).toString(16)}` });
                return;
            }
            if (a === "halt" || a === "reset_halt") {
                const info = await OCD.haltinfo();
                ST.tgt_state = info.state; ST.halt_reason = info.reason; ST.halt_pc = info.pc;
            }
            reply({ out: a });
        }
        else if (t === "step") {
            const pc = await OCD.step(msg.n || 1);
            const info = await OCD.haltinfo();
            const regs = await OCD.regs();
            ST.regs = regs;
            reply({ out: pc ? `pc=0x${pc.toString(16)}` : "",
                    state: info.state, reason: info.reason,
                    regs: Object.fromEntries(Object.entries(regs).map(([k, v]) => [k, "0x" + v.toString(16).padStart(8, "0")])) });
        }
        else if (t === "ctrl") {
            const v = await OCD.setTrace(msg.pc, msg.exc);
            reply({ dwt_ctrl: "0x" + v.toString(16),
                    warn: ST.pc_on && ST.exc_on ? "同开会饱和" : "" });
        }
        else if (t === "mem") {
            const [addr, size] = resolveSym(msg.addr);
            if (addr === null) { reply({ error: "无法解析" }); return; }
            const w = parseInt(msg.w) || 4;
            const n = Math.max(1, Math.min(256, parseInt(msg.len) || 64));
            const vals = await OCD.memRead(addr, n, w);
            const bs = Buffer.concat(vals.map(v => {
                const b = Buffer.alloc(w); b.writeUIntLE(v, 0, w); return b;
            }));
            reply({ addr: "0x" + addr.toString(16), w,
                    vals: vals.map(v => "0x" + v.toString(16).padStart(2 * w, "0")),
                    ascii: bs.toString("latin1").replace(/[^\x20-\x7e]/g, ".") });
        }
        else if (t === "memw") {
            const [addr] = resolveSym(msg.addr);
            if (addr === null) { reply({ error: "无法解析" }); return; }
            await OCD.memWrite(addr, parseInt(msg.value) || 0, parseInt(msg.w) || 4);
            reply({ out: "ok" });
        }
        else if (t === "bp") {
            const act = msg.action || "", kind = msg.kind || "bp";
            if (act === "clr") { await OCD.bpDel(); await OCD.wpDel(); }
            else {
                const [addr] = resolveSym(msg.addr);
                if (addr === null) { reply({ error: "无法解析" }); return; }
                if (kind === "bp") {
                    if (act === "add") await OCD.bpAdd(addr, msg.len === 4 ? 4 : 2);
                    else await OCD.bpDel(addr);
                } else {
                    if (act === "add") await OCD.wpAdd(addr, msg.len || 4, msg.acc || "w");
                    else await OCD.wpDel(addr);
                }
            }
            const { bps, wps } = await OCD.bps();
            ST.bps = bps; ST.wps = wps;
            reply({ bps: bps.map(b => ({ addr: "0x" + b[0].toString(16), len: b[1], hw: true })),
                    wps: wps.map(w => ({ addr: "0x" + w[0].toString(16), len: w[1], acc: { 5: "r", 6: "w", 7: "a" }[w[2]] || "?" })) });
        }
        else if (t === "watch") {
            const act = msg.action || "";
            const name = String(msg.name || "").trim();
            if (act === "add") {
                let addr = null, size = 4, disp = name;
                const ent = ST.sym_by_name.get(name);
                if (ent) { addr = ent[0]; size = ent[1]; if (size > 4) size = 4; }
                else { addr = parseInt(name); if (isNaN(addr)) { reply({ error: "符号未找到" }); return; } }
                if (!ST.watches.find(w => w.addr === addr && w.name === disp)) {
                    ST.watches.push({ name: disp, addr, size, fmt: msg.fmt || "u32",
                        win: parseInt(msg.win) || 1, series: [], n: 0 });
                }
                reply({ ok: true });
            } else if (act === "del") {
                ST.watches = ST.watches.filter(w => w.name !== name);
                reply({ count: ST.watches.length });
            } else if (act === "clr") {
                ST.watches = []; reply({ count: 0 });
            } else if (act === "rate") {
                ST.watch_ms = Math.max(50, Math.min(5000, parseInt(msg.ms) || 50));
                reply({ watch_ms: ST.watch_ms });
            } else if (act === "setfmt") {
                const w = ST.watches.find(w => w.name === name);
                if (w) { w.fmt = msg.fmt || "u32"; reply({ ok: true }); }
                else reply({ error: "未找到" });
            } else if (act === "setwin") {
                const w = ST.watches.find(w => w.name === name);
                if (w) { w.win = Math.max(0, Math.min(4, parseInt(msg.win) || 1)); reply({ ok: true }); }
                else reply({ error: "未找到" });
            }
        }
        else if (t === "eventport") {
            ST.event_port = Math.max(0, Math.min(31, parseInt(msg.port) || 2));
            reply({ event_port: ST.event_port });
        }
        else if (t === "swocfg") {
            ST.swo_traceclk = Math.max(1e6, Math.min(3e8, parseInt(msg.traceclk) || 72e6));
            if (msg.baud) ST.swo_baud = parseInt(msg.baud);
            const actual = await OCD.swoTpiu(ST.swo_traceclk, ST.swo_baud);
            reply({ traceclk: ST.swo_traceclk, out: `RX ${actual} Hz` });
        }
        else if (t === "sym") {
            reply({ elf: ST.elf_path, count: ST.syms.length, objects: ST.objs.length,
                    syms: [...ST.syms.slice(0, 60).map(([a, s, n]) => ({ a: "0x" + a.toString(16), sz: s, n, t: "F" })),
                           ...ST.objs.slice(0, 400).map(([a, s, n]) => ({ a: "0x" + a.toString(16), sz: s, n, t: "O" }))] });
        }
        else if (t === "disfuncs") {
            const d = await ensureDisasm(false);
            if (d.error) { reply({ error: d.error }); return; }
            reply({ funcs: d.funcs.map(f => ({ a: "0x" + f[0].toString(16),
                n: f[2], sz: (f[1] || f[0]) - f[0] })) });
        }
        else if (t === "disasm") {
            const srcMode = msg.src === 1 || msg.src === true;
            const d = await ensureDisasm(srcMode);
            if (d.error) { reply({ error: d.error }); return; }
            if (!msg.addr && !msg.func) {
                reply({ func: null, rows: d.rows });
                return;
            }
            const addr = msg.addr ? parseInt(msg.addr) : null;
            const funcName = msg.func || null;
            let fn = null;
            if (funcName) fn = d.funcs.find(f => f[2] === funcName);
            else if (addr !== null) fn = d.funcs.find(f =>
                f[0] <= addr && addr < (f[1] || f[0] + 0x100));
            if (!fn) { reply({ func: null, rows: d.rows.slice(0, 200) }); return; }
            const start = fn[0], end = fn[1] || fn[0] + 0x100;
            const rows = d.rows.filter(r =>
                r[0] === "f" ? true :
                r[0] === "s" ? true :
                r[1] >= start && r[1] < end);
            reply({ func: { a: "0x" + fn[0].toString(16), n: fn[2], sz: end - fn[0] },
                    rows });
        }
    } catch (e) {
        reply({ error: e.message });
    }
}

const OBJDUMP_PATHS = [
    process.env.OBJDUMP,
    "/home/victor/Arise2/toolchains/gcc-arm-none-eabi-9-2019-q4-major/bin/arm-none-eabi-objdump",
    "arm-none-eabi-objdump",
].filter(Boolean);

function findObjdump() {
    const { execFileSync } = require("child_process");
    for (const p of OBJDUMP_PATHS) {
        try { execFileSync(p, ["--version"], { stdio: "ignore" }); return p; }
        catch (e) { try { execFileSync(p, ["--version"], { stdio: "pipe" }); return p; } catch(e2) {} }
    }
    return null;
}

async function ensureDisasm(withSrc) {
    const key = withSrc ? "src" : "plain";
    if (ST.disasm && ST._disasmKey === key) return ST.disasm;
    const objdump = findObjdump();
    if (!objdump) return { error: "找不到 arm-none-eabi-objdump（设 OBJDUMP 环境变量）" };
    const args = withSrc ? ["-S", "-d", ST.elf_path] : ["-d", ST.elf_path];
    return new Promise((resolve) => {
        execFile(objdump, args, { maxBuffer: 20 * 1024 * 1024 }, (err, stdout) => {
            if (err) { resolve({ error: err.message }); return; }
            const rows = [], funcs = [];
            const lines = stdout.split("\n");
            let curFn = null;
            const fnRe = /^([0-9a-f]+) <(.+)>:$/;
            const insnRe = /^\s*([0-9a-f]+):\t(.*)$/;
            for (const line of lines) {
                const fm = line.match(fnRe);
                if (fm) {
                    curFn = [parseInt(fm[1], 16), null, fm[2]];
                    funcs.push(curFn);
                    rows.push(["f", fm[2], parseInt(fm[1], 16)]);
                    continue;
                }
                if (!curFn) continue;
                const im = line.match(insnRe);
                if (im) {
                    const addr = parseInt(im[1], 16);
                    const rest = im[2];
                    const tabIdx = rest.indexOf("\t");
                    let bytes = rest, insn = "";
                    if (tabIdx >= 0) {
                        bytes = rest.slice(0, tabIdx).trim();
                        insn = rest.slice(tabIdx + 1).trim();
                    } else {
                        const sp = rest.indexOf(" ");
                        if (sp >= 0) { bytes = rest.slice(0, sp); insn = rest.slice(sp + 1); }
                    }
                    rows.push(["i", addr, bytes, insn]);
                } else if (line.trim() && !line.match(/^\s*$/)) {
                    rows.push(["s", line.trim()]);
                }
            }
            // 补齐没有结束地址的函数
            for (let i = 0; i < funcs.length; i++) {
                if (funcs[i][1] === null) {
                    funcs[i][1] = i + 1 < funcs.length ? funcs[i + 1][0] : funcs[i][0] + 0x100;
                }
            }
            const result = { funcs, rows };
            ST.disasm = result; ST._disasmKey = key;
            resolve(result);
        });
    });
}

function resolveSym(text) {
    const t = String(text || "").trim();
    if (!t) return [null, 0];
    const v = parseInt(t);
    if (!isNaN(v)) return [v, 4];
    const ent = ST.sym_by_name.get(t);
    return ent ? [ent[0], ent[1]] : [null, 0];
}

// ============================================================ HTTP 服务器
const UI_HTML = `<!doctype html>
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
   <option value="i8">i8</option><option value="f32">f32</option></select>
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
return h?\`\${h}:\${String(m).padStart(2,"0")}:\${String(x).padStart(2,"0")}\`
:\`\${String(m).padStart(2,"0")}:\${String(x).padStart(2,"0")}\`};
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
  ws=new WebSocket(\`ws://\${location.host}/ws\`);
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
    \`<span class="pill\${p===curCh?" on":""}" onclick="openCon(\${p})">ch\${p}\${p===ep?'<span class="ep"> ⚑evt</span>':''}</span>\`).join("");}
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
  $("cmdout").textContent=r.error||(\`DWT_CTRL = \${r.dwt_ctrl}\`+(r.warn?\` ⚠ \${r.warn}\`:""));}
async function target(a){const r=await post("/api/target",{action:a});
  $("cmdout").textContent=r.error||(r.out||"(no output)");
  con.textContent+=\`\\n[jtag_tool] \${a}: \${r.out||r.error||""}\\n\`;
  if($("autoscroll").checked)con.scrollTop=con.scrollHeight;}
async function rawCmd(){const c=$("cmd").value;if(!c)return;$("cmd").value="";
  $("cmdout").textContent="…";
  const r=await post("/api/cmd",{cmd:c});
  $("cmdout").textContent="";
  con.textContent+=\`\\n[jtag_tool] > \${c}\\n\${r.out||r.error||""}\\n\`;
  if($("autoscroll").checked)con.scrollTop=con.scrollHeight;}
async function swoCfg(){
  const r=await post("/api/swocfg",{traceclk:parseInt($("swotc").value)||72000000,
    baud:parseInt($("swobaud").value)||8000000});
  $("elf_info").textContent=r.error||\`SWO 重配: \${r.out||""}\`;}

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
        const row=document.querySelector(\`.drow[data-a="\${a}"]\`);
        if(row){row.scrollIntoView({block:"center",behavior:"smooth"});}
      });
    }
  }
  window._prevState=s.tgt_state;
  const rb=$("dbgRun");
  if(rb)rb.innerHTML=s.tgt_state==="halted"?"▶ 运行":"⏸ Halt";
  const bcls=s.tgt_state==="halted"?"hlt":s.tgt_state==="running"?"run":"unk";
  const btxt=s.tgt_state==="halted"
    ?\`⏸ \${s.halt_reason||"halted"}\${s.halt_pc?" @"+s.halt_pc:""}\`
    :s.tgt_state==="running"?"▶ 运行中":"—";
  $("t_state").innerHTML=\`<span class="b \${bcls}">\${esc(btxt)}</span>\`;
  $("t_mhz").textContent=s.mhz?s.mhz.toFixed(2)+" MHz":"—";
  $("t_pc").textContent=s.pc_total.toLocaleString();
  $("t_exc").textContent=s.exc_events.toLocaleString();
  $("t_rs").textContent=s.resyncs.toLocaleString();
  $("t_pc_on").checked=s.pc_on;$("t_exc_on").checked=s.exc_on;
  $("t_pc2").checked=s.pc_on;$("t_exc2").checked=s.exc_on;
  $("sb_up").textContent=fmtUp(s.uptime_s);
  $("sb_right").textContent=\`\${UI_VER} · \${s.elf.split("/").pop()} · \${s.symbols} 符号 · \${s.objects?"+":""}\${s.objects||0} 变量 · ovf \${s.overflows.toLocaleString()}\`;
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
 $("p_hint").textContent=s.total?\`top1：\${s.top[0].sym}（\${s.top[0].pct.toFixed(1)}%）\`
   :"未开启——工具栏打开「PC 采样」";
 const mx=Math.max(1,...s.top.map(x=>x.n));
 /* 表格 DOM 只建一次（按地址签名）——8fps innerHTML 重建会把 mousedown
    的节点在 mouseup 前销毁，浏览器不生成 click = "点不中"（实测） */
 const sig=s.top.map(r=>r.pc).join(",");
 const tb=$("p_tbl").querySelector("tbody");
 if(sig!==_profSig){
   _profSig=sig;_profRows={};
   tb.innerHTML=s.top.map((r,i)=>
    \`<tr id="pr\${i}"><td style="min-width:180px"><div class="bar"><i class="pbar" style="width:0%"></i></div></td>
     <td>\${esc(r.sym)}\${profInsn(r.pc)?\` <span class="mono" style="color:var(--faint)">; \${esc(profInsn(r.pc))}</span>\`:""} <span class="cbtn" style="cursor:pointer" data-jump="\${r.pc}" title="反汇编定位">⇢</span></td><td class="mono paddr">\${r.pc}</td>
     <td class="pcnt">0</td><td class="ppct">0%</td></tr>\`).join("")
    ||\`<tr><td colspan=5 class="empty">未开启或暂无样本</td></tr>\`;
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
   \`<div style="width:\${r.pct}%;background:\${DCOLORS[i%8]}" title="\${esc(r.sym)} \${r.pct.toFixed(1)}%">\${r.pct>=6?esc(r.sym.split("+")[0]):""}</div>\`).join("")
  +(s.top.length>6&&other>0.3?\`<div style="width:\${other}%;background:#33414f" title="其他 \${other.toFixed(1)}%">…</div>\`:"");
 $("distleg").innerHTML=seg.map((r,i)=>
   \`<span><span style="color:\${DCOLORS[i%8]}">■</span> \${esc(r.sym.split("+")[0])} \${r.pct.toFixed(1)}%</span>\`).join("");
}
function renderExc(s){
 $("e_events").textContent=s.events.toLocaleString();
 $("e_ret").textContent=s.ret_avg_us??"—";
 $("e_mis").textContent=s.mispaired.toLocaleString();
 $("e_rs").textContent=s.resyncs.toLocaleString();
 $("e_hint").textContent=s.events?\`最近事件：\${s.recent.length?excName(s.recent[s.recent.length-1].exc):"—"}\`
   :"未开启——工具栏打开「异常跟踪」";
 /* 表格建一次（按异常号签名），20fps 只改文本/条宽——
    innerHTML 全量重建会抖（列宽跳+hover 丢失，实测同剖析表） */
 const tb=$("e_tbl").querySelector("tbody");
 const mx=Math.max(1,...s.irqs.map(x=>x.n));
 const esig=s.irqs.map(q=>q.exc).join(",");
 if(esig!==window._excSig){
   window._excSig=esig;window._excRows={};
   tb.innerHTML=s.irqs.map((q,i)=>
    \`<tr id="er\${i}"><td style="min-width:140px"><div class="bar"><i class="ebar" style="width:0%"></i></div></td>
     <td class="mono">\${q.exc}</td><td>\${esc(excName(q.exc))}</td><td class="ecnt">0</td>
     <td class="eh">—</td><td class="et">—</td><td class="ep">—</td></tr>\`).join("")
    ||\`<tr><td colspan=7 class="empty">未开启或暂无事件</td></tr>\`;
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
 if(!ev.length){$("tl_lanes").innerHTML=\`<div class="empty" style="padding:10px">暂无事件</div>\`;
   $("tlx0").textContent=$("tlx1").textContent="";return;}
 const t0=ev[0].ms,t1=ev[ev.length-1].ms,span=(t1-t0)||1e-3;
 const lanes=[...new Set(ev.map(e=>e.exc))].slice(0,5);
 $("tl_lanes").innerHTML=lanes.map(ex=>{
   const marks=ev.filter(e=>e.exc===ex||e.k==="ret").map(e=>
     \`<div class="ev \${e.k}" style="left:calc(\${((e.ms-t0)/span*100).toFixed(2)}% - 2px)"
       title="@\${e.ms.toFixed(3)}ms \${e.k} #\${e.exc} \${esc(excName(e.exc))}"></div>\`).join("");
   return \`<div class="lane"><span class="axis"></span><span class="lname">\${esc(excName(ex))} (#\${ex})</span>\${marks}</div>\`;
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
 $("elf_info").textContent=\`\${symsCache.elf} · \${symsCache.count} 符号\`;
 const tb=$("sy_tbl").querySelector("tbody");
 tb.innerHTML=symsCache.syms.map(r=>
   \`<tr><td class="mono">\${r.a}</td><td>\${r.sz}</td><td>\${esc(r.n)}\${r.t==="O"?
    \` <button class="cbtn" style="margin-left:6px" onclick="symWatch('\${esc(r.n)}')">＋监控</button>\`:""}</td></tr>\`).join("");
}
/* ================= 调试：寄存器 / 内存 / 断点 ================= */
let lastRegs={};
function rnum(n){const m=n.match(/^r(\\d+)$/i);return m?+m[1]:99;}
function renderDebug(s){
 try{
  $("dbgreason").textContent=
    s.state==="halted"?\`\${s.reason||"halted"} @\${s.pc||"??"}\`
    :s.state==="running"?"运行中——Halt 后显示":"jtag_tool 未连（板上先停 openocd，tmux 跑 jtag_tool --serve）";
  const g=$("reggrid");
  if(s.state!=="halted"||!Object.keys(s.regs).length){
    g.innerHTML=\`<span class="hint">\${s.state==="running"?"目标运行中——工具栏 Halt 后显示寄存器快照":"无寄存器快照"}</span>\`;
    lastRegs={};
  }else{
    const keys=Object.keys(s.regs).sort((a,b)=>rnum(a)-rnum(b)||a.localeCompare(b));
    let html=keys.map(k=>{
      const chg=lastRegs[k]!==undefined&&lastRegs[k]!==s.regs[k];
      return \`<div class="rg\${chg?" chg":""}"><span class="n">\${esc(k)}</span><span class="v">\${s.regs[k]}</span></div>\`;
    }).join("");
    const xk=keys.find(k=>/^xpsr$/i.test(k));
    if(xk){const x=parseInt(s.regs[xk],16);
      const fl=[["N",31],["Z",30],["C",29],["V",28]].map(([n,b])=>
        \`<span class="flag\${(x>>>b)&1?" on":""}">\${n}</span>\`).join("");
      const ipsr=x&0x1ff;
      html=\`<div class="regwide">\${s.regs[xk]}&nbsp; \${fl} <span style="color:var(--dim)">IPSR=\${ipsr}（\${ipsr?excName(ipsr):"Thread"}）</span></div>\`+html;}
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
 $("meminfo").textContent=\`\${r.addr} 起 \${r.vals.length} 单元\`;
 renderMem(r.vals,r.ascii);}
function renderMem(vals,ascii){
 const per=8;let rows="";
 for(let i=0;i<vals.length;i+=per){
  const row=vals.slice(i,i+per);
  const arow=ascii.slice(i*per*memW,(i+1)*per*memW);
  rows+=\`<tr><td class="a">0x\${(memBase+i*per*memW).toString(16).padStart(8,"0")}</td>\`+
   row.map((v,j)=>\`<td class="c" onclick="memEdit(\${i*per+j},this)">\${v}</td>\`).join("")+
   \`<td class="a">\${esc(arow)}</td></tr>\`;}
 $("memh").textContent=\`值（点击编辑 · \${memW===4?"字":memW===2?"半字":"字节"}）\`;
 $("memtbl").querySelector("tbody").innerHTML=rows;}
function memEdit(idx,td){
 if(memBase===null)return;
 const addr="0x"+(memBase+idx*memW).toString(16);
 const v=prompt(\`\${addr} 新值（hex/dec）：\`,td.textContent.trim());
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
 else $("meminfo").textContent=\`\${a}（\${fmt}）已加入「变量」页\`;}
async function symWatch(n){
 const r=await post("/api/watch",{action:"add",name:n,fmt:"u32",win:0});
 if(r.error)alert(r.error);
 else $("elf_info").textContent=\`\${n} 已加入「变量」页（格式可在表格里改）\`;}
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
   s.bps.map(b=>\`<tr><td>断点\${b.hw?" hw":""}</td><td class="mono">\${b.addr}</td><td>\${b.len}</td><td>—</td>
     <td><button class="cbtn" onclick="bpDel('bp','\${b.addr}')">删</button></td></tr>\`).join("")+
   s.wps.map(w=>\`<tr><td>观察点 \${w.acc}</td><td class="mono">\${w.addr}</td><td>\${w.len||"—"}</td><td>—</td>
     <td><button class="cbtn" onclick="bpDel('wp','\${w.addr}')">删</button></td></tr>\`).join("")
   ||\`<tr><td colspan=5 class="empty">无</td></tr>\`;
}

/* ================= 反汇编 ================= */
let disCache=null,disLastPc=null,disFuncsLoaded=false;
async function loadFuncs(){
 const r=await wreq({t:"disfuncs"});
 if(r.error){$("disinfo").textContent=r.error;return;}
 $("dfuncs").innerHTML=r.funcs.map(f=>
  \`<div onclick="disFuncSel('\${f.n.replace(/'/g,"\\\\'")}')">\${esc(f.n)} <span style="color:var(--faint)">\${f.sz}B</span></div>\`).join("")
  ||\`<div class="empty" style="padding:10px">无函数（先在「目标」页加载 ELF）</div>\`;}
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
                                :{action:"add",kind:"bp",addr:\`0x\${a.toString(16)}\`,len:2});
 const has=!!ex;
 const now=!has&&!(r&&r.error);            /* 成功后的新状态 */
 if(r.bps){bpsCache={bps:r.bps,wps:r.wps||[]};renderBps();}
 if(el){el.textContent=now?"●":"○";el.classList.toggle("on",now);}  /* 原地翻转：
   不全量 disRender——DOM 重建会吞掉紧随的第二次点击（toggle 不稳） */}
function disRender(){
 if(!disCache||!disCache.rows)return;
 let html="";
 for(const r of disCache.rows){
  if(r[0]==="f")html+=\`<div class="drow fn">\${esc(r[1])} @ 0x\${r[2].toString(16)}</div>\`;
  else if(r[0]==="s")html+=\`<div class="drow src">\${esc(r[1])}</div>\`;
  else html+=\`<div class="drow" data-a="\${r[1]}"><span class="dgp\${disBPAt(r[1])?" on":""}" onclick="disBP(\${r[1]},this)" title="断点增删">\${disBPAt(r[1])?"●":"○"}</span><span class="da">0x\${r[1].toString(16).padStart(8,"0")}</span><span class="db">\${esc(r[2])}</span>\${esc(r[3])}</div>\`;}
 $("dpre").innerHTML=html;
 disPcMark();}
function disPcMark(){
 document.querySelectorAll(".drow.pchit").forEach(e=>e.classList.remove("pchit"));
 const pc=window._pc;
 if(!pc||!disCache)return;
 const row=document.querySelector(\`.drow[data-a="\${parseInt(pc,16)}"]\`);
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
   if(f)$("disinfo").textContent=\`\${f.n} · PC \${window._pc}\`;
 }else disPcMark();
 if(window._pc!==disLastPc){disLastPc=window._pc;
   const row=document.querySelector(\`.drow[data-a="\${a}"]\`);
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
     const row=document.querySelector(\`.drow[data-a="\${a}"]\`);
     if(row){
       document.querySelectorAll(".drow.pchit").forEach(e=>e.classList.remove("pchit"));
       row.classList.add("pchit");
       row.scrollIntoView({block:"center",behavior:"smooth"});
       $("disinfo").textContent=\`定位 0x\${a.toString(16)}\`;
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
         const row=document.querySelector(\`.drow[data-a="\${focus}"]\`);
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
function wNum(w,v){             // 原始 u 值 -> 按 fmt 的数值
  if(v==null)return null;
  switch(w.fmt){
    case"i32":return v|0;
    case"u16":return (v>>>0)&0xFFFF;
    case"i16":{const x=v&0xFFFF;return x>=0x8000?x-0x10000:x;}
    case"u8":return (v>>>0)&0xFF;
    case"i8":{const x=v&0xFF;return x>=0x80?x-0x100:x;}
    case"f32":_f32u[0]=v>>>0;return _f32f[0];
    default:return v>>>0;}}
function wStr(w,v){const x=wNum(w,v);return x==null?"—":
  w.fmt==="f32"?x.toFixed(4):w.fmt==="hex"?"0x"+x.toString(16):String(x);}
async function watchAdd(){
 const n=$("wname").value.trim();if(!n)return;
 const r=await post("/api/watch",{action:"add",name:n,fmt:$("wfmt").value});
 $("winfo").textContent=r.error||\`已添加 \${n}\`;
 if(!r.error){$("wname").value="";wTrig.fired=false;wDisp=null;wFrozenOk=false;}}
async function watchRate(){
 const r=await post("/api/watch",{action:"rate",ms:parseInt($("wrate").value)||500});
 $("winfo").textContent=r.error||\`采样周期 \${r.watch_ms}ms\`;}
async function watchDel(n){await post("/api/watch",{action:"del",name:n});}
async function wFmtSet(n,f){
  const r=await post("/api/watch",{action:"setfmt",name:n,fmt:f});
  $("winfo").textContent=r.error||\`\${n} 格式 → \${f}\`;}
async function wWinSet(n,k){
  const r=await post("/api/watch",{action:"setwin",name:n,win:parseInt(k)});
  $("winfo").textContent=r.error||\`\${n} → 波形窗\${k}\`;}
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
 const opts=wDisp?wDisp.watches.map(w=>\`<option>\${esc(w.name)}</option>\`).join(""):"";
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
    localStorage.setItem("swo_watches",sig.split(",").join("\\n"));
    const tb=$("w_tbl").querySelector("tbody");
    tb.innerHTML=s.watches.map((w,i)=>{
      const[lo,hi]=wRange(w);
      const fsel=["u32","i32","hex","u16","i16","u8","i8","f32"].map(f=>
        \`<option\${f===w.fmt?" selected":""}>\${f}</option>\`).join("");
      const wsel=[1,2,3,4].map(k=>
        \`<option value="\${k}"\${(w.win??1)===k?" selected":""}>窗\${k}</option>\`).join("");
      return \`<tr id="wr\${i}"><td><span style="color:\${DCOLORS[i%8]}">■</span></td><td>\${esc(w.name)}</td>
      <td class="mono">\${w.addr}</td><td><select style="width:58px" onchange="wFmtSet('\${esc(w.name)}',this.value)">\${fsel}</select></td>
      <td><select style="width:56px" onchange="wWinSet('\${esc(w.name)}',this.value)">\${wsel}</select></td><td class="mono cur">—</td>
      <td class="mono lo">\${fmtY(lo,w.fmt==="f32")}</td><td class="mono hi">\${fmtY(hi,w.fmt==="f32")}</td><td class="cnt">0</td>
      <td><button class="cbtn" onclick="watchDel('\${w.name}')">删</button></td></tr>\`;}).join("")
     ||\`<tr><td colspan=10 class="empty">无 watch</td></tr>\`;
    s.watches.forEach((w,i)=>{
      const tr=$("wr"+i);
      if(tr)wRows[w.name]={cur:tr.querySelector(".cur"),
                           cnt:tr.querySelector(".cnt"),
                           lo:tr.querySelector(".lo"),hi:tr.querySelector(".hi")};});
    $("wleg").innerHTML=s.watches.map((w,i)=>
      \`<span><span style="color:\${DCOLORS[i%8]}">■</span> \${esc(w.name)}（\${w.fmt}）</span>\`).join("");
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
  x.fillText(\`窗 \${k}\`,pad.l+2,y0+16);
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
      x.fillText(wTrig.fired?\`TRIG'D \${tag}\`:\`TRIG \${tag}\`,W-pad.r-110,y0-3>0?y0-3:10);}}
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
  x.fillText(\`\${w.name}（\${w.fmt}）\`,ox,oy+8);
  bc.forEach((c,b)=>{
    const h=c/mx*gh;
    x.fillStyle=c?"#4fc3f7":cvc("#1a2431","#dbe3ea");
    x.fillRect(ox+b*gw/BUCKETS,oy+12+gh-h,gw/BUCKETS-1.5,h);});
  x.fillStyle=cvc("#5b6b7c","#66778a");x.font="9.5px monospace";
  x.fillText(fmtY(lo,w.fmt==="f32"),ox,oy+gh+26);
  const rt=fmtY(hi,w.fmt==="f32");x.fillText(rt,ox+gw-x.measureText(rt).width,oy+gh+26);
  x.fillText(\`N=\${N}\`,ox+gw/2-10,oy+gh+26);});}
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
 let html=\`<div style="color:#8fa0b0">@ \${(t-g.t1).toFixed(2)}s</div>\`;
 const all=wDisp?wDisp.watches:[];
 band.vars.forEach(w=>{
   let best=null,bd=1e18;
   for(const pt of w.series){const d=Math.abs(pt[0]-t);
     if(d<bd){bd=d;best=pt;}}
   if(best)html+=\`<div><span style="color:\${DCOLORS[all.indexOf(w)%8]}">■</span> \`+
     \`\${esc(w.name)} = <b>\${esc(wStr(w,best[1]))}</b></div>\`;});
 hov.innerHTML=html;
 hov.style.display="block";
 hov.style.left=Math.min(hv.mx+14,g.W-170)+"px";
 hov.style.top=(hv.my+10)+"px";}
/* watch 列表恢复（localStorage）+ 符号补全 */
{const l=(localStorage.getItem("swo_watches")||"").split("\\n").filter(Boolean);
 for(const e of l){const [n,f,g]=e.split("|");
   if(n)post("/api/watch",{action:"add",name:n,fmt:f||"u32",win:parseInt(g)||1});}
 {const tb=localStorage.getItem("swo_wtb");if(tb!==null)$("wtb").value=tb;}
 wreq({t:"sym"}).then(r=>{
   if(r&&r.syms){
     const objs=r.syms.filter(q=>q.t==="O").map(q=>q.n);
     $("wl_syms").innerHTML=objs.map(n=>\`<option value="\${esc(n)}">\`).join("");}});}
/* ================= 时间线（异常 + ITM 事件归并） ================= */
function renderTl2(s){
 try{
  $("w_ev").textContent=s.events.length;
  $("w_des").textContent=s.desync;$("w_sdr").textContent=s.stamp_drops;
  $("w_evp").textContent=window._evport??2;
  const ev=s.events;
  const box=$("tl2_lanes");
  if(!ev.length){box.innerHTML=\`<div class="empty" style="padding:10px">暂无事件（异常跟踪 / 事件流固件未开）</div>\`;
    return;}
  const t0=ev[0].ms,t1=ev[ev.length-1].ms,span=(t1-t0)||1e-3;
  const key=e=>e.src==="exc"?"exc:"+e.exc:"evt:"+e.type;
  const lanes=[...new Set(ev.map(key))].slice(0,10);
  box.innerHTML=lanes.map(k=>{
    const isExc=k.startsWith("exc:");
    const marks=ev.filter(e=>key(e)===k).map(e=>{
      const left=\`left:calc(\${((e.ms-t0)/span*100).toFixed(2)}% - 2px)\`;
      return isExc
        ?\`<div class="ev \${e.k}" style="\${left}" title="@\${e.ms.toFixed(3)}ms \${e.k} #\${e.exc} \${esc(excName(e.exc))}"></div>\`
        :\`<div class="ev evt" style="\${left}" title="@\${e.ms.toFixed(3)}ms 事件\${e.type} arg=\${e.arg}"></div>\`;}).join("");
    const name=isExc?\`\${excName(+k.slice(4))} (#\${k.slice(4)})\`:\`事件类型 \${k.slice(4)}\`;
    return \`<div class="lane"><span class="axis"></span><span class="lname">\${esc(name)}</span>\${marks}</div>\`;}).join("");
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
</script></body></html>`;

const server = http.createServer(async (req, res) => {
    const url = new URL(req.url, `http://${req.headers.host}`);
    const p = url.pathname;

    if (req.headers.upgrade === "websocket") return; // 由 upgrade 事件处理

    if (req.method === "GET" && p === "/") {
        res.writeHead(200, { "Content-Type": "text/html; charset=utf-8",
            "Cache-Control": "no-store", "Content-Length": Buffer.byteLength(UI_HTML) });
        res.end(UI_HTML);
        return;
    }

    // API 端点
    try {
        if (req.method === "GET") {
            if (p === "/api/status") { json(res, apiStatus()); return; }
            if (p === "/api/pcstats") { json(res, apiPcstats()); return; }
            if (p === "/api/excstats") { json(res, apiExcstats()); return; }
            if (p === "/api/events") { json(res, apiEvents()); return; }
            if (p === "/api/symbols") {
                json(res, { elf: ST.elf_path, count: ST.syms.length, objects: ST.objs.length,
                    syms: ST.syms.slice(0, 60).map(([a, s, n]) => ({ a: "0x" + a.toString(16), sz: s, n, t: "F" }))
                    .concat(ST.objs.slice(0, 400).map(([a, s, n]) => ({ a: "0x" + a.toString(16), sz: s, n, t: "O" }))) });
                return;
            }
            if (p === "/api/bps") {
                const { bps, wps } = await OCD.bps();
                json(res, { bps: bps.map(b => ({ addr: "0x" + b[0].toString(16), len: b[1], hw: true })),
                             wps: wps.map(w => ({ addr: "0x" + w[0].toString(16), len: w[1], acc: { 5: "r", 6: "w", 7: "a" }[w[2]] || "?" })) });
                return;
            }
        }
        if (req.method === "POST") {
            const body = await readBody(req);
            if (p === "/api/target") {
                const a = body.action || "";
                if (a === "halt") await OCD.halt();
                else if (a === "resume") await OCD.resume();
                else if (a === "reset") await OCD.memWrite(0xE000ED0C, 0x05FA0004);
                else if (a === "reset_halt") {
                    await OCD.memWrite(0xE000ED0C, 0x05FA0004);
                    const pc = await OCD.halt();
                    json(res, { action: a, out: `halted pc=0x${(pc || 0).toString(16)}` });
                    return;
                }
                json(res, { action: a, out: a });
                return;
            }
            if (p === "/api/step") {
                const pc = await OCD.step(body.n || 1);
                json(res, { out: pc ? `pc=0x${pc.toString(16)}` : "" });
                return;
            }
            if (p === "/api/ctrl") {
                const v = await OCD.setTrace(body.pc, body.exc);
                json(res, { dwt_ctrl: "0x" + v.toString(16) });
                return;
            }
            if (p === "/api/cmd") {
                json(res, { out: (await OCD.cmd(String(body.cmd || "").slice(0, 200))).slice(-2000) });
                return;
            }
            if (p === "/api/swocfg") {
                ST.swo_traceclk = Math.max(1e6, Math.min(3e8, parseInt(body.traceclk) || 72e6));
                if (body.baud) ST.swo_baud = parseInt(body.baud);
                const actual = await OCD.swoTpiu(ST.swo_traceclk, ST.swo_baud);
                json(res, { traceclk: ST.swo_traceclk, out: `RX ${actual} Hz` });
                return;
            }
            if (p === "/api/bp") {
                // 复用 ws 处理
                await handleWsMessage({ pending: new Map(), tab: "debug" }, { t: "bp", ...body, id: 999 });
                const { bps, wps } = await OCD.bps();
                json(res, { bps: bps.map(b => ({ addr: "0x" + b[0].toString(16), len: b[1], hw: true })),
                             wps: wps.map(w => ({ addr: "0x" + w[0].toString(16), len: w[1], acc: { 5: "r", 6: "w", 7: "a" }[w[2]] || "?" })) });
                return;
            }
            if (p === "/api/watch") {
                const act = body.action || "";
                if (act === "add") {
                    handleWsMessage({ pending: new Map() }, { t: "watch", ...body, id: 998 });
                    json(res, { count: ST.watches.length });
                } else if (act === "del" || act === "clr" || act === "rate" || act === "setfmt" || act === "setwin") {
                    handleWsMessage({ pending: new Map() }, { t: "watch", ...body, id: 998 });
                    json(res, { ok: true });
                } else {
                    json(res, { watches: ST.watches.map(w => ({
                        name: w.name, addr: "0x" + w.addr.toString(16), size: w.size, fmt: w.fmt, win: w.win || 1,
                        series: w.series.slice(-600).map(([t, v]) => [Math.round(t * 1000) / 1000, v]) })) });
                }
                return;
            }
            if (p === "/api/mem") {
                const [addr] = resolveSym(body.addr);
                if (addr === null) { json(res, { error: "无法解析" }, 400); return; }
                if (body.value !== undefined) {
                    await OCD.memWrite(addr, parseInt(body.value) || 0, parseInt(body.w) || 4);
                    json(res, { addr: "0x" + addr.toString(16), out: "ok" });
                } else {
                    const w = parseInt(url.searchParams.get("w")) || parseInt(body.w) || 4;
                    const n = parseInt(url.searchParams.get("len")) || parseInt(body.len) || 64;
                    const vals = await OCD.memRead(addr, n, w);
                    const bs = Buffer.concat(vals.map(v => { const b = Buffer.alloc(w); b.writeUIntLE(v, 0, w); return b; }));
                    json(res, { addr: "0x" + addr.toString(16), w,
                        vals: vals.map(v => "0x" + v.toString(16).padStart(2 * w, "0")),
                        ascii: bs.toString("latin1").replace(/[^\x20-\x7e]/g, ".") });
                }
                return;
            }
        }
        // ---- Python 兼容端点（UI 走 ws，这些给脚本/外部工具用）----
        if (req.method === "GET") {
            if (p === "/api/regs") {
                json(res, { state: ST.tgt_state, reason: ST.halt_reason,
                    pc: ST.halt_pc !== null ? "0x" + ST.halt_pc.toString(16).padStart(8, "0") : null,
                    regs: Object.fromEntries(Object.entries(ST.regs).map(([k, v]) => [k, "0x" + v.toString(16).padStart(8, "0")])) });
                return;
            }
            if (p === "/api/dwt") {
                json(res, { mhz: Math.round(ST.mhz * 100) / 100,
                    exc_ps: Math.round(ST.exc_ps * 10) / 10,
                    sleep_pct: Math.round(ST.sleep_pct * 10) / 10,
                    raw: { cyc: "0x" + ST.dwt_raw[0].toString(16).padStart(8, "0"),
                           cpi: ST.dwt_raw[1], exc: ST.dwt_raw[2],
                           slp: ST.dwt_raw[3], lsu: ST.dwt_raw[4], fold: ST.dwt_raw[5] },
                    note: "cpi/exc/slp/lsu/fold 为 8 位计数器，忙循环下每 ~35µs 回绕一次" });
                return;
            }
            if (p === "/api/channels") {
                const ports = [0, ...[...ST.chan_text.keys()].filter(p => ST.chan_text.get(p).length >= 16)].sort((a,b)=>a-b);
                json(res, { ports, counts: Object.fromEntries([...ST.chan_text.keys()].map(p => [String(p), ST.chan_text.get(p).length])),
                    event_port: ST.event_port });
                return;
            }
            if (p === "/api/watches") {
                json(res, { watches: ST.watches.map(w => ({
                    name: w.name, addr: "0x" + w.addr.toString(16).padStart(8, "0"),
                    size: w.size, fmt: w.fmt, win: w.win || 1,
                    series: w.series.map(([t, v]) => [Math.round(t * 1000) / 1000, v]) })) });
                return;
            }
        }
        if (req.method === "POST" && p === "/api/eventport") {
            const body2 = await readBody(req);
            ST.event_port = Math.max(0, Math.min(31, parseInt(body2.port) || 2));
            json(res, { event_port: ST.event_port });
            return;
        }
        res.writeHead(404); res.end();
    } catch (e) {
        json(res, { error: e.message }, 500);
    }
});

// WebSocket upgrade
server.on("upgrade", (req, socket, head) => {
    if (req.url === "/ws") wsSession(req, socket);
    else socket.destroy();
});

// ============================================================ 启动
async function main() {
    loadSymbols(ELF_PATH);

    // 解析板地址并连接
    const ip = await resolveBoard();
    ST._boardIp = ip;
    console.log(`swo_web (Node.js): http://0.0.0.0:${PORT}  board=${BOARD_HOST} → ${ip}  elf=${path.basename(ELF_PATH)}`);

    // 后台任务
    swoLoop().catch(console.error);
    withRetry(tgtLoop, 250).catch(console.error);
    withRetry(dwtLoop, 250).catch(console.error);
    setInterval(() => watchLoop().catch(() => {}), ST.watch_ms);

    server.listen(PORT, "0.0.0.0", () => {
        console.log(`HTTP listening on :${PORT}`);
    });
}

main().catch(e => { console.error(e); process.exit(1); });
