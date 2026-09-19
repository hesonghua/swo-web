# swo_web — J-Trace 式 SWO/调试 Web 控制台

单文件零依赖（python3 标准库）的 PC 侧工具，配合板上 `jtag_tool --serve`，
把 EBAZ4205（Zynq）+ `jtag_swd_dbg` PL IP 变成 Cortex-M3 目标的实时调试/
追踪工作站。openocd 链路已退役——SWO 数据由 jtag_tool 自己从 IP FIFO 收取
直推 TCP，彻底绕开 openocd 转发层的停摆问题。

```
┌───────────── PC ─────────────┐      ┌────────── 板上 (elink.local) ──────────┐
│ 浏览器 http://127.0.0.1:8080 │      │ tmux: jtag_tool --serve               │
│   │ WebSocket(8fps 推送)     │      │   ├─ 命令口 :5555  二进制帧协议        │
│ swo_web.py（HTTP+ws+SWO解析）│◄───► │   └─ SWO 流口 :5556 原始字节直推       │
│   ├─ Ocd 客户端 ─────────────│TCP   │        │                              │
│   └─ SWO 流客户端 ───────────│TCP   │   jtag_swd_dbg IP @0x43C00000 (PL)    │
└──────────────────────────────┘      │        ├─ SWD 引擎 ──► STM32F1 目标   │
                                      │        └─ SWO RX (边沿CDR, 1M) ◄──┤  │
                                      └───────────────────────────────────────┘
```

## 启动

**板上**（每次板子重启后要做一次）：

```sh
ssh root@elink.local          # 密码 123456；IP 常漂移，别用固定 IP
tmux new -d -s jtag './jtag_tool --serve'
# 确认 banner 出现 "serve: 二进制命令口 :5555"；openocd 必须不在跑
```

**PC**：

```sh
cd boards/ebaz4205_esp32/swo-web
python3 swo_web.py            # 默认连 elink.local，HTTP :8080，ELF 用默认 swotest
# 或指定： python3 swo_web.py 192.168.10.176 8080 /path/to/firmware.elf
```

浏览器打开 `http://127.0.0.1:8080`，顶栏 **jtag_tool / SWO 两个 LED 变绿**
即全链路就绪。页面异常时先 **Ctrl+Shift+R 强刷**（浏览器缓存旧页面会表现
为"死了"）。

## 顶栏

- **状态徽标**：`⏸ breakpoint @0x…`（停机原因+PC）/ `▶ 运行中`
- **CPU**：DWT CYCCNT 实时测频（目标 72 MHz 时显示 72.0x）
- **样本/事件/resync**：PC 采样与异常跟踪累计
- **PC 采样 / 异常跟踪**开关、Halt / Resume / Reset·Halt / Reset·Run

## 八个视图

| Tab | 用途 | 数据来源 |
|---|---|---|
| 控制台 | ITM 多通道文本终端（ch pill 切换），底部命令箱直通 jtag_tool shell | SWO ITM port0/1-31 |
| 执行剖析 | PC 采样热点直方图/表，点 `⇢` 跳反汇编 | SWO DWT PC 包 |
| 异常分析 | 异常 entry/exit/ret 配时（handler µs/触发延迟/周期） | SWO DWT 异常包 |
| 时间线 | DWT 异常 + ITM 事件流按 GTC 归并的多 lane 图 | SWO |
| 性能计数 | CYCCNT/CPICNT/EXCCNT… 原始值 + MHz/异常率/睡眠% 走势 | SWD 轮询（250ms） |
| **调试** | **三栏：寄存器网格（xPSR 解码/单步）‖ 反汇编（函数列表/跳转/源码交错/PC 高亮）‖ 内存浏览器 + 断点/观察点** | SWD + ELF |
| **变量** | **多模式变量可视化追踪（见下）** | SWD 轮询（默认 50ms） |
| 目标 | ELF 路径展示、DWT 开关、SWO 重配、符号表（变量行＋监控） | — |

## 变量可视化追踪（重点）

### 添加变量

- 输入框：**ELF 全局变量名**（带自动补全，STT_OBJECT）或 **`0x2000000C`
  式原始地址**（无符号也能看）
- 免手敲入口：调试页内存浏览器**「＋监控」**按钮（符号/地址 + 字宽自动
  选 u32/u16/u8，输入框同样带符号补全）；目标页符号表每个变量行
  **「＋监控」**按钮
- 格式：`u32 / i32 / hex / u16 / u8 / f32`（f32 按 IEEE754 重解释；u16/u8
  自动做字节偏移提取）
- 采样率：右侧输入框 `50`~`5000` ms 回车（相邻地址自动合并成一次突发读）
- watch 列表存浏览器 localStorage，刷新/重开自动恢复；换 ELF 按名字重解析

### 四种视图（一键切换）

| 视图 | 效果 |
|---|---|
| **曲线** | 示波器式：固定时基滑窗（2s~60s/全部，默认 10s，记住选择），多窗口各自 Y 量程共享时基，MATLAB 盒式网格，hover 按窗口取值实时刷新 |
| 仪表盘 | 每变量一个表盘，min~max 自动归一，当前值大字 |
| 位视图 | 寄存器/标志逐位 LED 实时跳变（8 位一组标号） |
| 直方图 | 值分布（40 桶小倍数图） |

### 触发与暂停

- **触发**（阈值单次，示波器式）：选变量 + `>`/`<` + 阈值 → 点按钮"武装"；
  命中瞬间画面冻结在触发点并画红色标记线；再点按钮重新武装
- **暂停显示**：后台采样不停（曲线数据继续积累），恢复时无断层

### 推送管线

采样 50ms → 增量推送（只发新点，~200B/包）→ ws 20fps → 仅变更单元格原地
更新 DOM。600 点（50ms 下 30s）后自动回绕，画面持续滚动。

## 调试功能（调试 tab，三栏）

- **左栏·寄存器**：Halt 后网格实时刷新（250ms），变化的寄存器高亮；
  单步 ×1/×4；「⇢ 反汇编定位」跳到当前 PC
- **中栏·反汇编**：函数列表点击跳转；跳转框支持符号/地址；剖析热点
  `⇢` 定位；目标停止时自动跟随 PC 高亮；「源码交错」走 objdump -S
  （需编译 -g）。ELF 自动用 `swotest/swotest.elf`（目标页可换）
- **右栏·内存与断点**：字/半字/字节查看，点单元格改值，符号名当地址；
  FPB 硬件断点（符号或地址，半字/4 字节，M3 上软件断点无效一律 hw）；
  DWT 观察点（读/写/读写）。断点/观察点免 halt 随时下，一键全清

## SWO 配置（目标 tab）

- 连接时自动代配 `swo_tpiu 72M / 8M`（v4 小数-N CDR，精确频率匹配）
- **波特率可切**：1M / 4M / 8M（默认）/ 12M，目标页下拉选择
  | 档位 | PC 采样 | 异常事件 | 说明 |
  |---|---|---|---|
  | 1M | 7K/s（10%） | ✓ 满速 | 兼容旧设 |
  | 4M | 28K/s（40%） | ✓ 满速 | |
  | **8M** | **57K/s（81%）** | **✓ 满速** | **推荐默认** |
  | 12M | 63K/s（90%） | 26% | 信号边缘，不推荐 |
- 目标时钟变了（如复位初期 HSI 8M）→ 填新 traceclk 点「重配」
- 10s 静默自动踢活（目标 SWO 输出偶发静默卡死，看门狗自动重配复活）

## HTTP API（脚本化）

```
GET  /api/status            全量状态 JSON
GET  /api/pcstats | /api/excstats | /api/events | /api/channels
GET  /api/mem?addr=0x20000000&len=64&w=4
GET  /api/console/stream    控制台 SSE
POST /api/target  {"action":"halt|resume|reset|reset_halt"}
POST /api/step    {"n":4}
POST /api/bp      {"action":"add|del|clr","kind":"bp|wp","addr":"...","len":2,"acc":"w"}
POST /api/mem     {"addr":"0x20000008","value":"0x1234","w":4}
POST /api/watch   {"action":"add|del|clr|rate","name":"g_sine","fmt":"f32","ms":50}
POST /api/ctrl    {"pc":true,"exc":false}
POST /api/cmd     {"cmd":"mdw 0xE0001000 1"}     # 直通 jtag_tool shell
POST /api/swocfg  {"traceclk":72000000}
```

WebSocket `/ws`：UI 实时通道（status + 当前 tab 增量载荷，50ms 节奏）。

## 已知问题与限制

- **控制台文本乱码**：swotest 的 printf 流在线上存在字节级异常（疑似物理
  层 3bit 滑动类问题，FE=0），变量/调试/剖析功能不受影响。待专项。
- **PC 采样满速 ≈400KB/s 饱和 1M SWO 线**：与异常跟踪同开会断流，分开开；
  饱和丢包属目标侧限制，自愈机制保证流不断。
- **换固件**：jtag_tool 无 flash 编程器，需短暂起 openocd：
  `openocd -f /root/stm32f1-swo.cfg -c init -c "program /root/xxx.elf verify reset" -c shutdown`，
  完后停 openocd 再起 `--serve`
- **板上单客户端**：5555/5556 各只收一个连接；调试别开第二个实例
- **板子会整机重启/IP 漂移**：一律用 `elink.local`；重启后重跑「启动」两步

## 故障排查

| 症状 | 处置 |
|---|---|
| 页面全死/点了没反应 | Ctrl+Shift+R 强刷；再查 swo_web 进程与 8080 端口 |
| 命令超时（API/命令箱无响应） | 多半板子重启了：重起 tmux jtag_tool；PC 侧 swo_web 重启 |
| 目标（STM32）复位/掉电后链路卡死 | **自动恢复**：连续命令失败后板侧自动重探（reprobe）SWD 链路；也可手动 `reprobe`（命令箱）或等 swo_web 连错自动触发 |
| SWO LED 红 | 看 swo_state；10s 静默看门狗会自动踢活，也可目标页手动重配 |
| CPU MHz 显示 0 | CYCCNT 未跑，任意开关一次 PC 采样即恢复 |
| 波形不动 | 旧页面缓存 → 强刷；确认目标在跑、采样率没设 5000ms |
| halt 后单步无效 | 目标可能在 WFI 循环里，PC 不动属正常 |

## 回归

改 swo_web.py 后必跑：`python3 mock_ocd_test.py`，**ALL PASS** 才算好。

---
板侧工具文档见 `../jtag_tool.md`；IP/引脚/协议细节见仓库记忆与
`src/ebit_z7010_esp32/hdl/jtag_swd_dbg.v`。
