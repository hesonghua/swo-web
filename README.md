# swo_web — Real-Time SWO Debug Web Console

Single-file, zero-dependency web-based debugging workstation for Cortex-M
targets. Connects to an on-board `jtag_tool --serve` backend over TCP,
parses the SWO/ITM/DWT byte stream, and serves a full-featured single-page
UI in your browser.

## Features

### Eight Views

| Tab | Description |
|-----|-------------|
| Console | Multi-channel ITM text terminal, command box |
| Profiling | PC sampling hotspot histogram with instruction annotation |
| Exception | IRQ timing analysis (handler µs, trigger delay, period) |
| Timeline | DWT exceptions + ITM events merged on GTC timeline |
| Perf Counters | CYCCNT/CPICNT/etc + live CPU frequency |
| Debug | Registers, disassembly (objdump), breakpoints, memory |
| Variables | Multi-window oscilloscope, gauges, bit view, histogram |
| Target | Symbol table, DWT toggles, SWO baud config |

### Variable Watch (5 visualization modes)

- **Line chart**: oscilloscope-style with fixed timebase (2s–60s), multi-window
  (independent Y-range per window), MATLAB-style boxed grid + MATLAB color palette
- **Gauge**: analog dial per variable
- **Bit view**: per-bit LED grid for registers/flags
- **Histogram**: value distribution (40 buckets)
- **Threshold trigger**: single-shot with pre/post capture, trigger point centered
- **Hide option**: win=0 keeps table updating without drawing in any chart window

### Debug Features

- IDE-style toolbar (halt/step/reset)
- Disassembly with source interleave (`objdump -S`), PC auto-follow on halt
- Click-to-toggle hardware breakpoints in the disassembly gutter
- FPB breakpoints + DWT watchpoints (no halt required to set)
- Memory browser with symbol name lookup + inline editing

## Quick Start

```bash
# 1. On the Zynq board (as root):
./jtag_tool --serve

# 2. On your PC:
python3 swo_web.py [board_host] [port] [elf_path]

# 3. Open browser:
http://localhost:8080
```

## Backend Options

| Version | File | Best for |
|---------|------|----------|
| Python | `swo_web.py` | Full features (disassembly, objdump), single file |
| Node.js | `swo_web.js` | Heavy PC sampling + exception tracking simultaneously |

Both versions share the same embedded UI and API. Switch by killing one
and starting the other (same port).

## SWO Baud Rates

| Rate | PC Sampling | Exception | Notes |
|------|-------------|-----------|-------|
| 1M | 7K/s (10%) | Full | Legacy safe |
| 4M | 28K/s (40%) | Full | |
| **8M** | **57K/s (81%)** | **Full** | **Recommended** |
| 12M | 63K/s (90%) | 26% | Signal integrity edge |

Requires IP v4 (fractional-N CDR). Baud rate switchable at runtime from
the Target tab.

## REST API (for scripting)

```
GET  /api/status             Full status JSON
GET  /api/pcstats            PC sampling histogram
GET  /api/excstats           Exception timing stats
GET  /api/events             Timeline events
GET  /api/mem?addr=...&len=64&w=4
POST /api/target             {"action":"halt|resume|reset"}
POST /api/step               {"n":4}
POST /api/bp                 {"action":"add|del","kind":"bp|wp","addr":"..."}
POST /api/mem                {"addr":"0x...","value":"0x..."}
POST /api/watch              {"action":"add|del|rate|setwin","name":"..."}
POST /api/ctrl               {"pc":true,"exc":false}
POST /api/cmd                {"cmd":"mdw 0x... 4"}
```

WebSocket `/ws` for real-time push (20fps incremental updates).

## Files

| File | Description |
|------|-------------|
| `swo_web.py` | Python version (stdlib only, HTML embedded) |
| `swo_web.js` | Node.js version (stdlib only, HTML embedded) |
| `mock_ocd_test.py` | Offline regression test (fake jtag_tool backend) |
| `README.md` | This file |

## Prerequisites

- **Board side**: Zynq with `jtag_swd_dbg` IP + `jtag_tool` binary
- **PC side**: Python 3.6+ (stdlib) or Node.js 18+ (stdlib)
- **Optional**: `arm-none-eabi-objdump` for disassembly view

## Running Tests

```bash
python3 mock_ocd_test.py   # ALL PASS required after any change
```
