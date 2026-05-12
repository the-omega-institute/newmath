# Spec: rule110/ ground-up minimal-trust BEDC kernel — vertical slice init

状态: **v1 — brainstorming 批准 2026-05-12, 待 user spec 审核**
日期: 2026-05-12
范围: 在 `rule110/` 目录建立 BEDC FKernel 的 ground-up minimal-trust 替代基底, init 阶段产出 Mark.lean 等价 vertical slice (cyclic tag layer + Rule 110 evaluator 独立 ship)

---

## 0. 一句话目的

**在 5-7 天 sprint 内 ship 一个 ANSI C minimal-trust evaluator 套件 (Rule 110 + cyclic tag) + 复用 BEDC GroundCompiler bit-string encoding convention + 把 `lean4/BEDC/FKernel/Mark.lean` 的 4 个 `msame` theorem 编码成 self-consistent 可执行 manifest, 作为 BEDC 内容下降到 Rule 110 substrate 的 vertical slice proof-of-concept**。

---

## 1. 设计哲学: 元层 trust 持续向下

主 BEDC (`lean4/BEDC/`) 当前坐在 Lean 4 CIC 上, 元层信任面 = 几万行 Lean kernel + stdlib (虽然 0-axiom)。本 spec 把 BEDC 内容的一小段 (Mark.lean) push 到一个 *再降一档* 的 substrate:

- **cyclic tag system** (Post 1943, Cook 2004 复用为 universal-construction 中间层): 元层 trust = ~80 行 ANSI C evaluator
- **Rule 110 elementary cellular automaton** (Cook 2004 证 universal): 元层 trust = ~50 行 ANSI C evaluator + 8-entry truth table
- **Rule 110 比 cyclic tag 再低一档** (规则数 fix, 局部均匀), 但二者都在公开计算理论的"最小 universal class"内

vertical slice **不**在 init 阶段做 Cook construction (cyclic tag → Rule 110 universal encoder)。理由见 §3 调研评估: Cook construction 实际 25 天 wall clock (AI 协作弱项), 不在 init scope。Rule 110 evaluator 独立 ship + binary counter toy demo 证明 Rule 110 substrate 自身 universality, BEDC 内容编码 *目前* 落在 cyclic tag substrate; Cook construction 连接层留 milestone-2。

---

## 2. 五个 locked design 决定 (经 user brainstorming 选)

1. **Init scope**: 完整 Mark.lean vertical slice (4 个 theorem)
2. **Evaluator 语言**: ANSI C (元层 trust 表面最小)
3. **Theorem encoding**: Hybrid — 每 theorem 给 enumeration 版 + algorithm 版 manifest
4. **Cross-check**: Self-consistent only — vertical slice 不 cross-check Lean FKernel, 独立 ground-up 起点
5. **跟主 BEDC 关系**: Sibling experiment 并行 — 分支只动 `rule110/`, 不 modify `lean4/` 或 `papers/bedc/`

---

## 3. Scope (B-option locked, A 调研后排除)

### 3.1 In-scope (5-7 day sprint)

- `rule110/` 目录结构 + README + LICENSE + Makefile
- Rule 110 evaluator (`evaluator/rule110.c`, ~50 行 ANSI C) + binary counter toy demo
- Cyclic tag system evaluator (`evaluator/cyclic_tag.c`, ~80 行 ANSI C)
- GroundCompiler bit-string encoding convention port (`encoder/groundcompiler_encoding.c`, ~120 行 ANSI C)
- Mark.lean 4 theorem 的 cyclic tag manifest (8 文件: enum + algo 各一)
- Self-consistent test suite (~500 行 ANSI C 总)
- 文档 (README + trust_chain.md + manifest_format.md + theorem_encoding.md)

### 3.2 Out-of-scope (留 future milestones)

- **Cook construction encoder** (cyclic tag → Rule 110): 调研评估 25 天 wall clock 中位值, 是 multi-week project 不是 init sprint 事
- **Rule 110 substrate manifests** (`.r110` 文件): 依赖 Cook construction, 一起留 milestone-2
- **BHist / Ext / SigRel / NameCert** 等 FKernel 其余 inductive 移植: 留 milestone-3 + 之后
- **Cross-check 跟 Lean FKernel**: vertical slice 标准是 self-consistent, 不依赖 Lean 作 oracle
- **CI workflow** (`.github/workflows/`): init 完成 + 跑 1-2 周稳定后再加, init 阶段 *本地可 reproduce* 已够

### 3.3 调研发现 (排除 A-option 的依据)

| 调研项 | 数据 |
|---|---|
| Cook 2004 paper 长度 | 40 页, "substantially constructive but not drop-in implementable" |
| 公开 GitHub Cook construction 实现 | 最 mature 是 [slightknack/machine-110](https://github.com/slightknack/machine-110) (Rust ~300 LOC, 11 stars, 作者 explicitly 承认 incomplete + abandoned) |
| 公开 minimal-trust ANSI C universal Cook encoder | **零** |
| LLM (GPT-4 / Claude / Codex) 已知成功做 Cook construction | **零** 直接证据; 任务 profile (long-range geometric invariants, off-by-one fatal, sparse training data) 是 LLM 弱项 |
| Cook encoder wall clock 修订 | 下界 12 天 / 中位 25 天 / 上界 60+ 天 (跟 Lean mathlib boilerplate 不同 magnitude) |

A 选项 (含 Cook construction) 不 init scope 范围。

### 3.4 Known risks (5-7 day sprint 内可能挑战的点)

- **P_eq cyclic tag productions 设计 (Day 4-5 主要风险)**: algo 版 manifest 共享的 `P_eq` 程序需要在 cyclic tag substrate 上实现"两个 event 解码后 bit-by-bit 相等"判定。cyclic tag system 没有内置 register / branch 概念, 需要把"比较"编码成 productions sequence (推测 5-15 条 productions, 但具体设计非平凡, 可能花 0.5-1 day 调试)。若 Day 4 调不通, fallback: enum 版先 ship (覆盖 all 4 theorem), algo 版降级为 Day 6+ stretch goal
- **GroundCompiler encoding edge cases**: Lean 版 `DecEvent` 用 dependent option type + fuel pattern, ANSI C port 必须仔细 mirror DecodeFuel 语义不让无限递归。Round-trip test 是主要 catch net
- **Wikipedia collatz CT 当 oracle 失败**: 若该 example 在我们 evaluator 不复现已知 trajectory, 说明 cyclic tag evaluator 实现 bug, 需要 root-cause (debug 时间不可预先估), 通过本 spec acceptance criteria 之前必须 root-cause-fix 不 hand-wave 过去

---

## 4. 架构: trust chain

```
┌────────────────────────────────────────────────────────────────┐
│  rule110/  (sibling to lean4/, papers/bedc/)                   │
│                                                                │
│  Layer 0: ANSI C compiler + machine semantics                  │
│           (universal, 工业标配, 不 audit)                      │
│  ↓                                                             │
│  Layer 1: Rule 110 evaluator (evaluator/rule110.c, ~50 行)     │
│           8-entry truth table {0,1,1,1,0,1,1,0} + 一个 for-loop│
│           ✓ ship + binary counter toy demo 验证自身 universal  │
│  ↓                                                             │
│  Layer 2: Cyclic tag evaluator (evaluator/cyclic_tag.c, ~80 行)│
│           Post 1943 + Cook 2004 standard semantics              │
│           ✓ ship + Wikipedia collatz-like CT example 跑通       │
│  ↓                                                             │
│  Layer 3: GroundCompiler-convention encoder                    │
│           (encoder/groundcompiler_encoding.c, ~120 行)         │
│           ANSI C reimplement of BodyEncoding / EventEncoding / │
│           DecEvent / DecodeFuel (from BEDC GroundCompiler)     │
│  ↓                                                             │
│  Layer 4: Mark.lean equivalent cyclic tag manifests            │
│           (manifests/mark/*.{enum,algo}.ct, 8 文件)             │
│  ↓                                                             │
│  Layer 5: Self-consistent test suite (tests/*.c)               │
│           32 assertions across 8 manifests + Layer A unit tests│
│                                                                │
│  Layer 6 (out of scope): Cook construction encoder + .r110     │
│           manifests — milestone-2, 4+ 周 wall clock             │
└────────────────────────────────────────────────────────────────┘
```

设计原则:
- **三个 evaluator + encoder 互相独立**: Rule 110 不依赖 cyclic tag, cyclic tag 不依赖 encoder, encoder 是单向 (高级表示 → bit stream)
- **Layer 1 是最底信任面**: ~50 行 C 是 audit 重心
- **GroundCompiler 复用是 design wisdom, 不是代码耦合**: ANSI C 实现独立, encoding *convention* (escape rules, terminator, reject taxonomy) align 主 BEDC 让未来 BHist / Ext 移植自然继承
- **Self-consistent 标准**: "init done" = 同一 theorem 的 enum + algorithm manifest 在 cyclic tag evaluator 跑出预期一致结果, 跟 manual 算的预期对齐

---

## 5. 目录结构

```
rule110/
├── README.md                    # 项目宣言 + trust chain 图 + reproducibility
├── LICENSE                      # GPOL v1.0 (跟主 BEDC `LICENSE` 一致, 文件直接 copy)
├── Makefile                     # `make` build 全套, `make test` 跑全测
│
├── evaluator/                   # Layer 1+2
│   ├── rule110.c                # ~50 行: Rule 110 CA
│   ├── rule110.h                # API: step / run_n_steps / dump_state
│   ├── cyclic_tag.c             # ~80 行: cyclic tag system
│   ├── cyclic_tag.h             # API: step / run_until_halt / dump_tape
│   └── common.h                 # 共享 bit array primitives
│
├── encoder/                     # Layer 3
│   ├── groundcompiler_encoding.c  # ~120 行: BodyEncoding/EventEncoding/DecEvent ANSI C port
│   ├── groundcompiler_encoding.h
│   └── README.md                # 链接到 lean4/BEDC/GroundCompiler/ChannelEncoding.lean
│
├── manifests/                   # Layer 4
│   └── mark/
│       ├── msame_refl.enum.ct        # 2 cases enumerated
│       ├── msame_refl.algo.ct        # P_eq algorithm, 2 reflexive cases
│       ├── msame_symm.enum.ct        # 4 cases enumerated
│       ├── msame_symm.algo.ct        # P_eq + P_swap algorithm, 4 cases
│       ├── msame_trans.enum.ct       # 8 cases enumerated
│       ├── msame_trans.algo.ct       # P_eq + extractors algorithm, 8 cases
│       ├── msame_no_confusion.enum.ct  # 2 cases enumerated
│       └── msame_no_confusion.algo.ct  # P_eq algorithm, 2 reject cases
│
├── tests/                       # Layer 5
│   ├── test_rule110.c           # Layer A unit: static pattern + binary counter + boundary
│   ├── test_cyclic_tag.c        # Layer A unit: collatz CT + identity + STEPLIMIT
│   ├── test_encoder.c           # Layer B round-trip + 6 reject reason
│   └── test_mark.c              # Layer C: 32 assertions across 8 manifests
│
└── docs/
    ├── design.md                # 链接回本 spec
    ├── trust_chain.md           # 元层 trust 逐层 audit guide
    ├── manifest_format.md       # cyclic tag manifest spec + GroundCompiler convention 链接
    └── theorem_encoding.md      # 4 个 msame theorem 各自 encoding 的解释
```

**Design 选择解释**:

- `evaluator/` 跟 `encoder/` 拆开: evaluator 是"读 manifest 跑"的引擎, encoder 是"高级表示 → bit stream"的翻译, 职责不同
- Manifest 文件命名 `<theorem>.<encoding>.ct`: 维度 orthogonal, 一眼看清
- `tests/` 用 C 不用 shell / Python: 测试逻辑 ("跑 evaluator A on manifest B, 比对 expected") 直接 C, 不引入额外 trust
- 没 `lean4/` 或 `paper/` 目录: 严格 sibling experiment, 不 leak 主 BEDC 形态

---

## 6. ANSI C evaluator 设计

### 6.1 Rule 110 evaluator (`evaluator/rule110.c`)

```
数据结构:
  CellArray { uint8_t *cells; size_t len; }
  // 1 byte per cell (浪费 7 bit 换可读 audit, 不 bit-pack)

核心:
  static const uint8_t rule110_table[8] = {0,1,1,1,0,1,1,0};
  void step(CellArray *a):
    1. memcpy a→cells 到 buf
    2. for i in 0..a→len-1:
         left  = (i == 0)         ? 0 : buf[i-1];
         self  = buf[i];
         right = (i == a→len-1)   ? 0 : buf[i+1];
         a→cells[i] = rule110_table[(left<<2) | (self<<1) | right];
  void run_n_steps(CellArray *a, size_t n);
  void dump_state(CellArray *a, FILE *out);  // 每 cell '0'/'1', \n 结尾

I/O 协议 (text-based):
  stdin 行 1: 初始 bit pattern (ASCII '0'/'1')
  stdin 行 2: step 数 (decimal)
  stdout: final state after n steps

边界处理: fixed boundary, 边界外 = 0 (不 wrap, 不 grow)
错误: stdin 非 '0'/'1' → exit(1), 输出 stderr reject reason
```

### 6.2 Cyclic tag evaluator (`evaluator/cyclic_tag.c`)

```
数据结构:
  TagSystem {
    uint8_t **productions;       // 第 i 条产生式 bit string
    size_t   *prod_lens;
    size_t    num_productions;
    uint8_t  *tape;
    size_t    tape_len;
    size_t    tape_cap;          // 动态扩展
    size_t    pc;                // 当前指向第几条产生式
  }

核心 (Cook 2004 standard semantics):
  step(TagSystem *t):
    1. 如果 t→tape_len == 0: HALT_EMPTY (空 tape = 停机)
    2. head = t→tape[0]
    3. if head == 1: append productions[t→pc] to tape (tape_cap grow if needed)
       (pc 无论 head 0 还是 1 都前进)
    4. shift tape left by 1 (drop t→tape[0])
    5. t→pc = (t→pc + 1) % t→num_productions

  run_until_halt(t, max_steps):
    for _ in 0..max_steps:
      if t→tape_len == 0: return HALT_EMPTY;
      step(t);
    return HALT_STEPLIMIT;

I/O 协议:
  stdin 行 1: N (产生式数)
  stdin 行 2..N+1: 每条产生式 (ASCII bits)
  stdin 行 N+2: 初始 tape
  stdin 行 N+3: max_steps
  stdout: final tape + halt reason
```

### 6.3 共享纪律

- **完全 deterministic**: 同 input 永远同 output, 无系统时间 / 随机数 / 多线程
- **零外部依赖**: 只 `<stdio.h> <stdlib.h> <string.h> <stdint.h>`, 不用 mmap / pthread / 系统特定 API
- **text I/O**: ASCII '0'/'1' 直接读 stdin, 让 `cat manifest | ./eval` 这种 pipeline audit 透明
- **uint8_t 一字节存一 bit**: 浪费 storage 换 audit 友好, 不优化

---

## 7. GroundCompiler encoding convention 复用

参考: `lean4/BEDC/GroundCompiler/ChannelEncoding.lean` + `MinimalPrototype.lean`

### 7.1 Escape-based variable-length bit encoding

```
b0  →  b0            (literal, 1 bit: 0)
b1  →  b1 b0         (escaped, 2 bits: 10)
event terminator: b1 b1  (2 bits: 11)
EventEncoding(w : RawEvent) := BodyEncoding(w) ++ [b1, b1]
FlowEncoding(S : EventFlow) := concat of EventEncoding for each event in S
```

`b1 b1` 不可能在 escaped body 中出现 (因为 b1 总是被 escape 成 b1 b0), 所以可作 unambiguous terminator。

### 7.2 ANSI C port

`encoder/groundcompiler_encoding.c` 实现 4 个函数, 跟 Lean 版本 1:1:

```c
// body_encode([b0]) = "0"; body_encode([b1]) = "10"; body_encode([b0, b1]) = "010"
size_t body_encode(const uint8_t *in, size_t in_len, uint8_t *out, size_t out_cap);

// event_encode(w) = body_encode(w) ++ "11"
size_t event_encode(const uint8_t *in, size_t in_len, uint8_t *out, size_t out_cap);

// flow_encode([w1, w2]) = event_encode(w1) ++ event_encode(w2)
size_t flow_encode(/* ... */);

// dec_event 状态机 + DecodeFuel 防无限循环
// 返回 (decoded event, remaining stream) 或 RejectReason
DecodeResult dec_event(const uint8_t *in, size_t in_len, size_t fuel);
```

### 7.3 Reject taxonomy (从 `MinimalPrototype.lean:42` 复用)

```c
typedef enum {
    REJECT_NONE = 0,
    REJECT_DANGLING_ONE,           // bit stream 以 1 结尾未跟 0
    REJECT_UNFINISHED_EVENT,       // 无 11 terminator 就 EOF
    REJECT_NONBINARY_CHARACTER,    // 含 0/1 之外字符
    REJECT_EMPTY_INPUT_POLICY,     // 完全空 input
    REJECT_RESOURCE_BOUND_EXCESS,  // STEPLIMIT 或 fuel 耗尽
    REJECT_NONCANONICAL_DISPLAY    // parse OK 但不 LegalZStream
} RejectReason;
```

每 reject 出 `exit(1)` + stderr 一行 `reject: <reason> at offset N`。

---

## 8. Theorem encoding: 4 个 msame manifest

每 theorem 给 enum + algo 两版 manifest。BMark 是 finite 2-element domain, 所有 theorem trivially decidable by enumeration; algo 版是 **template for future BHist 移植** (BHist 不可 enumerate, 必须 algorithm), BMark-specific 阶段是 redundant 但保留为 design forcing function。

### 8.1 BMark encoding (under GroundCompiler convention)

```
EventEncoding(b0) = "0" ++ "11" = "011"      (3 bits)
EventEncoding(b1) = "10" ++ "11" = "1011"    (4 bits)
```

msame instance 编码: 两个 event 拼接 (`EventEncoding(m) ++ EventEncoding(n)`):

```
msame(b0, b0)  ↔  "011" ++ "011"   = "011011"     (6 bits)
msame(b0, b1)  ↔  "011" ++ "1011"  = "0111011"    (7 bits)
msame(b1, b0)  ↔  "1011" ++ "011"  = "1011011"    (7 bits)
msame(b1, b1)  ↔  "1011" ++ "1011" = "10111011"   (8 bits)
```

### 8.2 Theorem 1: `msame_refl : ∀ m, msame m m`

`msame_refl.enum.ct`:
```
# enum 版: PRODUCTIONS=none, 2 reflexive cases 直接 verify
PRODUCTIONS 0
ASSERTIONS 2
case b0_b0: input="011011", direct_constructor: msame := Eq, decoded events equal. ✓
case b1_b1: input="10111011", direct_constructor: same reasoning. ✓
```

`msame_refl.algo.ct`:
```
# algo 版: 一个 CT program P_eq 接受 (m, n) pair, accept iff decoded events equal
PRODUCTIONS [P_eq 的产生式, ~5-10 条, 实现 "两 events 解码后 bit-by-bit 相等"]
ASSERTIONS 2
input="011011" (b0, b0): expect P_eq halts with accept
input="10111011" (b1, b1): expect P_eq halts with accept
```

### 8.3 Theorem 2: `msame_symm : msame m n → msame n m`

enum 版: 4 cases (b0/b0, b0/b1, b1/b0, b1/b1), 各 trivial 或 vacuous (前件假 → 自动 true)

algo 版: P_eq + P_swap (输入 (m, n) → 输出 (n, m))。assertion: 对每 (m, n) input, P_eq(P_swap(input)) == P_eq(input)

### 8.4 Theorem 3: `msame_trans : msame a b → msame b c → msame a c`

enum 版: 8 cases (a, b, c) ∈ BMark³, 各 trivial 或 vacuous

algo 版: P_eq + 三 extractor (P_first / P_second / P_third)。assertion: 若 P_eq(a, b) ∧ P_eq(b, c), 则 P_eq(a, c) 必 accept

### 8.5 Theorem 4: `msame_no_confusion : (msame b0 b1 → False) ∧ (msame b1 b0 → False)`

enum 版: 2 cases, 直接 constructor analysis (b0 ≠ b1 by inductive distinctness)

algo 版: P_eq 在 (b0, b1) 和 (b1, b0) 上必须 reject

### 8.6 共用 program library

`P_eq` 在所有 algo 版共用。manifest 文件之间用 `include` 引用避免重复定义。

---

## 9. Testing 三层

### 9.1 Layer A: evaluator unit tests

```
test_rule110.c:
  - static pattern "00010000" 跑 100 步, 比对 Wolfram NKS Fig.1 已知 reference
  - binary counter toy: 特定初始 pattern 跑 N 步, 期望二进制递增 (验证 Rule 110 evolve 工作)
  - boundary: empty input / single cell / all-zero, 行为 deterministic 且 well-defined

test_cyclic_tag.c:
  - Wikipedia collatz-like CT (worked example), 应在 N 步内 halt 到已知 tape
  - identity CT (productions=[]): 入参 tape 直接消耗到空, halt
  - infinite CT: 验证 STEPLIMIT 触发, 不挂
```

### 9.2 Layer B: encoder round-trip + reject

```
test_encoder.c:
  - encode([b0]) == "011", decode("011") == [[b0]]
  - encode([b1]) == "1011", decode("1011") == [[b1]]
  - encode([b0, b1, b0]) == "01110110", decode("01110110") == [[b0], [b1], [b0]]
  - 6 reject reason: 给每个 reason 一个 trigger input, 比对 reject reason 枚举值
```

### 9.3 Layer C: manifest assertion

```
test_mark.c:
  - 跑 8 manifest × 各自 assertions (2 + 2 + 4 + 4 + 8 + 8 + 2 + 2 = 32 总 assertions)
  - 每 manifest: load + parse + invoke cyclic_tag evaluator on each input + compare halt-with-marker
  - 任何一条 assertion 挂 → make test exit 1
```

---

## 10. Day-by-day milestones (5-7 day sprint)

```
Day 1:  rule110/ 目录 + git branch rule110 + README + LICENSE + Makefile 骨架
        evaluator/rule110.c (~50 行) + rule110.h + test_rule110.c (3 unit tests)
        `make test` 跑通 Layer A 第一组

Day 2:  evaluator/cyclic_tag.c (~80 行) + cyclic_tag.h + test_cyclic_tag.c
        Wikipedia collatz-like CT 跑通, Layer A 完整

Day 3:  encoder/groundcompiler_encoding.c (~120 行) 含 4 个核心函数
        + 6 reject reason enum + error path
        test_encoder.c round-trip + 6 reject test, Layer B 完整

Day 4:  manifests/mark/msame_refl.{enum,algo}.ct 设计 + 写出
        手算每 assertion 期望 output 写进 manifest header
        test_mark.c 实现 (跑 manifest, 比对 assertion)
        msame_refl 4 个 assertion 跑通

Day 5:  msame_symm + msame_trans + msame_no_confusion 各 enum+algo 共 6 manifest
        全 32 assertions 跑通

Day 6:  docs/{trust_chain,manifest_format,theorem_encoding}.md 写
        README 完整 含 reproducibility instructions + GroundCompiler 链接
        clean up: 检查 LOC 报告
        最终 `make clean && make && make test` 全绿

Day 7:  buffer / 修 bug / merge 准备 / 给 spec 加 lessons-learned addendum
```

---

## 11. Acceptance criteria ("init done")

- [ ] `make` build 全套 (rule110, cyclic_tag, encoder, all tests) 无 warning
- [ ] `make test` 跑 32 manifest assertions + Layer A + Layer B unit tests 全绿, exit 0
- [ ] 总 ANSI C LOC 报告: evaluator < 200, encoder < 200, tests < 500, **总 < 1000**
- [ ] README 含: 项目宣言 / trust chain 图 / 怎么 reproduce / GroundCompiler encoding 链接
- [ ] 8 个 manifest 文件 ASCII 可读, header 含 theorem statement + 期望 assertion
- [ ] git branch `rule110` push 到 remote, `main` 分支 lean4/ + papers/bedc/ 完全未触动
- [ ] 本 spec + docs/superpowers/plans/<plan>.md 都 commit 到 rule110 分支

---

## 12. Future milestones (out of scope, 这里只是 forward-looking)

### M2: Cook construction encoder (4+ 周 wall clock)

cyclic tag → Rule 110 universal encoder, ANSI C ≤ 1000 行。需要:
- ether pattern (14×7) 编码
- ~15 个 glider family 的 phase 跟踪
- collision lookup table (from Cook paper figures)
- 在 vertical slice 的 8 manifest 上 round-trip verify (cyclic tag run vs encoded-then-r110-run 一致)

启动条件: vertical slice 已 ship 稳定 + 有具体 BHist / Ext encoding 需求驱动 (单纯为 4 个 msame theorem 做 4 周 Cook construction ROI 太低)

### M3: BHist / Ext / SigRel 移植

- BHist (Empty | e0 | e1) 在 GroundCompiler convention 下自然延展 (EventFlow 已经 list of events, BHist 是 list of bits = 单个 event)
- Ext / SigRel 是 inductive Prop, encoding 成 "存在 CT program 见证 relation holds for given inputs"
- 启动条件: M2 之后, 有真实理由把 BHist 内容 push 到 Rule 110 substrate

### M4: NameCert / CompGap / PkgPol

FKernel 余下部分。规模约 50 周以上 wall clock 估算 (1061 theorem × 平均 4 hr/theorem AI-assisted, 但有 amortization)。

---

## 13. 已知不变量 (rule110/ 自身的纪律, 不引入主 BEDC)

- **0 binary dependency**: 只依赖 ANSI C stdlib `<stdio.h> <stdlib.h> <string.h> <stdint.h>`
- **0 fancy 优化**: 不 bit-pack, 不 SIMD, 不 multithread — audit 优先
- **0 build script complexity**: Makefile 一份, `make` + `make test` + `make clean` 三 target 完
- **0 documentation rot**: README + 3 个 doc/*.md 内容跟代码同 commit 改, 不留 stale 引用

---

## 14. 参考

- Cook, M. (2004). "Universality in Elementary Cellular Automata". *Complex Systems* 15(1): 1-40. ([Wolfram-hosted PDF](http://wpmedia.wolfram.com/sites/13/2018/02/15-1-1.pdf))
- Post, E. L. (1943). "Formal Reductions of the General Combinatorial Decision Problem". *American Journal of Mathematics* 65(2): 197-215.
- Martínez, G. J. et al. (2013). "Computation with competing patterns in Life-like automaton". [arXiv:1307.7951](https://arxiv.org/abs/1307.7951)
- `lean4/BEDC/GroundCompiler/ChannelEncoding.lean` (本 spec encoding convention 来源)
- `lean4/BEDC/GroundCompiler/MinimalPrototype.lean` (reject reason taxonomy 来源)
- `lean4/BEDC/FKernel/Mark.lean` (本 spec 要 encode 的 4 theorem 来源)
