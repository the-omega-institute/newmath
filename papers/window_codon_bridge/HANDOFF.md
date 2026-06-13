# Window6 ↔ codon-Q₆ 桥 daemon — 交接文档

新 session 读这一份就能接管。本分支 = `feat/window-codon-bridge`,worktree = `/Users/lexa/Desktop/lexa/omega/newmath-window-bridge`。

## 1. 使命(一句)
在抽象数学的 **forced Window6**(fibonacci_reality,现跑在另一台机器)与生物的 **codon-Q₆ 边界**(bio_reality,本机另一 worktree)之间,产出**结构性 forcing 证书**,并与 bio 数据分支双向通讯。**不是数据管线;是 forcing 证书工厂。**

完整背景 + 三个对应 + 三个猜想 + 反 numerology 证书框架:见同目录 `README.md`(必读)。

## 2. 引擎(精简,已验证跑通一轮)
不 fork 臃肿的 bio 引擎。核心三件 + registries:
- `tools/window_codon_bridge/supervisor.py` — 循环:load registries → 跑 open claim 的推导实验 → verdict → 写回 + append ledger → keep lane commit → sleep。`--once` 单轮;`--no-commit` 不提交;stop 哨兵 `tools/window_codon_bridge/.stop`。
- `tools/window_codon_bridge/runner.py` — 跑实验脚本(subprocess,cwd=worktree 根),解析最后一行 JSON verdict。
- `tools/window_codon_bridge/registries/{claims,experiments}.json` — 桥猜想 + 推导实验。
- `tools/window_codon_bridge/experiments/run_*.py` — 推导脚本,**emit 一行 JSON `{status, ...}`**。

**verdict 词汇(反 numerology 的核心)**:
- `certified` — 给出了**结构 forcing 论证**(不只是数字吻合)。
- `refuted` — 对应为假。
- `coincidence` — 数字吻合但**无结构 forcing**;必须显式标 coincidence,**不算成果**。
- `needs_derivation` — 还没法评估(脚本未写 / 数学未做)。
退出码:certified/coincidence→0,refuted→2,needs_derivation→3。

**无 churn 设计**:只有 `open`/`needs_rerun` 的 claim 会被跑;`certified/refuted/coincidence/needs_derivation` 都是终态,下轮自动跳过(不像 bio 出过的 needs_data thrash)。

## 3. 启动 daemon(launchctl)
plist 已生成:`tools/window_codon_bridge/window.codon.bridge.supervisor.20260613143849.plist`(label 同名,python=/opt/homebrew/bin/python3,interval 600s,KeepAlive)。
安装:
```
cp tools/window_codon_bridge/window.codon.bridge.supervisor.20260613143849.plist ~/Library/LaunchAgents/
launchctl load ~/Library/LaunchAgents/window.codon.bridge.supervisor.20260613143849.plist
launchctl list | grep window.codon.bridge          # 看 PID
```
改代码后:`touch tools/window_codon_bridge/.stop` → 等 PID 退 → 改 → `rm .stop` → `launchctl kickstart -k gui/$(id -u)/<label>`。
测试单轮(不装 daemon):`cd <worktree> && python3 tools/window_codon_bridge/supervisor.py --once --no-commit`。

## 4. 当前状态(已验证)
跑过 2 轮,commit `4d41687dd8`。3 个 claim:
- `bridge.window6_codon_q6.spectral_correspondence` (BC2) → **refuted**:Window6 粗 Markov 核谱 {1.0,0.093,−0.071,−0.174} ≠ bio λ_M/λ_R/μ(0.675/0.476/3.05;且 μ>1 不可能是随机核特征值)。脚本 `run_bc2_markov_kernel_spectrum.py`。
- `bridge.window6_codon_q6.cardinality_forcing` (BC1) → **needs_derivation**:无脚本。
- `bridge.window6_codon_q6.foldbin_codon_positions` (BC3) → **needs_derivation**:无脚本。

## 5. 下一步工作(给新 session)
1. **BC2-R1(精炼谱对应)**:先搞清 bio λ_M/λ_R/μ 的**真实构造**(读 bio `window_six_codon_tiles_at_the_code_layer` 及其生成代码;注意有个 "radial cubic check",μ 可能是标度/质量而非特征值),再试 Window6 **transfer-operator golden Perron 谱 / Green response**(不是粗 Markov 核)。写 `run_bc2r1_*.py` emit verdict。
2. **BC1(基数 forcing)**:构造显式映射 `标准码边界 → width-6 Fibonacci 词`,论证 \|R\|=13=F₇、21 家族=F₈ 是**必然**;数字吻合只 emit `coincidence`,有 forcing 论证才 `certified`。bio 经验接触由 Route L 提供(见 ledger / §6)。
3. **BC3(二次折叠)**:形式化 Foldbin 尾立方(c₇c₈c₉,seam-return ρ−s=3)→ 密码子 3 位/wobble 的映射;跟 bio Q^(2)(Route B,对丰度 FAILED)对照,判断 foldbin 的"正确二次对象"是否不同于失败的 codon-pair Q^(2)。
4. **(可选)全自治**:加一个 conjecture-proposal lane,从 Window6×codon-Q₆ 对应自动提新 BC + codex 派单写推导脚本,让 daemon 真正自驱(目前是被动跑已注册 claim)。
5. 推导脚本一律 **codex 作者**(像 BEDC),orchestrator 验真 + **严防 numerology**;fibonacci 的 Window6 数学**只读**引用(在另一台机器/另一 worktree,别改其分支)。

## 6. 与 bio 数据分支的双向通讯
`papers/window_codon_bridge/bridge_ledger.jsonl`(随 dev rollup 两边可见):
- **桥→bio**:猜想发起数据测。**BC1 正在测**:bio 在跑 `b_star_q6_boundary_set_biological_signature_powered`(Route L,detached,本机 bio worktree `/Users/lexa/Desktop/lexa/omega/newmath` 的 `/tmp/codex-routel.log`)——测"边界集 R 在真实生物有无签名"。结果出来回填 ledger BC1。
- **bio→桥**:bio 结构发现(Route K 最优方向 GC3 聚类 + 弱普适核;Route J f3=翻译选择代理)= 桥的推导靶子(ledger 已记 BIO-K-OPT / BIO-F3-DRIVER)。
- 协调:bio 那条线由原 session(我)继续盯;桥这条由新 session。两边只通过 ledger + dev rollup 通讯;跨分支消息由人/orchestrator 搬。

## 7. 关键参考(只读)
- 数学 Window6:`papers/fibonacci_reality/parts/forced_window_structure/`(markov-kernel-coarse-spectrum、fibonacci-horizon-seam-return-foldbin-unification、transfer-operator-golden-perron-spectrum、edge-flux-mod3、modpstar-571、green-spectral-response…)。本机这些子文件可能不全(fibonacci 去别机跑了);需要时从 fibonacci 分支/远端取。
- 生物 codon-Q₆:`papers/bio_reality/parts/codon_window_reality_boundary/window_six_codon_tiles_at_the_code_layer.tex`。

## 8. 运维注意
- **共享 .git**:本机 worktree(bio + 本桥)共享一个 .git。建 worktree / commit 前**等全局 git 静默**(`pgrep -x git`==0 且无 sync_with_auto_dev),避免抢 bio daemon 的 git lane(出过事故)。bridge worktree 有独立 index,commit 基本不抢 bio 的 index,但 ref 更新是共享的。
- bio daemon 跑在另一 worktree(launchctl `bio.reality.supervisor.20260525162508`),**别动它**。
- 命名纪律:无版本号(分支/文件/claim 都按内容主题)。
- git 提交用 `git config` 里的 email,别替换。

---

## Update 2026-06-13: BC1 head-started (by handoff session)

`tools/window_codon_bridge/experiments/run_bc1_cardinality_forcing.py` is wired + run. Verdict **coincidence**:
- Established: width-6 no-adjacent-one words = 21 = F8 (= 21 families); width-5 = 13 = F7 (= |R|).
- **Honest caveat that matters**: the 21↔21 count match is **encoding-independent** (any nucleotide→2-bit map is a codons↔64-words bijection, and there are always 21 no-adj words). So the count match picks out **nothing specific** about the genetic code — leans toward numerology unless a **code-structure-specific** map is built.
- **Your job on BC1**: construct a map that uses the actual synonymous-block / boundary structure (e.g. does the no-adjacent-one constraint, under a biologically-motivated encoding such as purine/pyrimidine = high/low bit, correspond to the family partition or to R?), with a necessity argument. Then upgrade to `certified` (real forcing) or downgrade to `refuted` (no structural map). Do NOT certify on counts alone.

Current claim states: BC1 `coincidence` (head-started), BC2 `refuted`, BC3 `needs_derivation`.
