# rule110 路线图

**项目**: BEDC 基于 Rule 110 元胞自动机 + 循环标签系统的最小信任 substrate.
**分支**: `rule110` (单 trunk; 历史里程碑 m2/m3 已归档到 `history/`).
**姊妹**: `lean4/BEDC/` (Lean 4 形式化, 人类可读 shorthand), `papers/bedc/` (LaTeX 论文).
**硬约束**: 零外部依赖, ANSI C99, Rule 110 + 循环标签系统作为唯二 substrate 原语.

---

## 核心原则

**BEDC 验证 = 有限 witness, 由计算 substrate 物理算出. Lean kernel 不在 BEDC 信任路径上.**

BEDC ontology 是有限可观察的: 每个 BEDC closure 由 `rule110/manifests/<module>/*.{enum,algo}.ct` 里的具体 assertion 表达. `lean4/BEDC/FKernel/*` 里的 `∀` 陈述是人类可读 shorthand, 表示"对所有 manifest 列出的具体实例都成立", **不是独立 universal 逻辑陈述**.

任何纯计算 substrate (cyclic tag / Rule 110 / 图灵机) 只能识别 Σ⁰₁. 这不是限制 — BEDC 不需要 Π⁰₁ universal quantifier.

---

## 双 Tier 架构

### Tier A: cyclic-tag witness (当前 ship 标准)

**信任路径**:

```
ANSI C 编译器
    ↓
evaluator/rule110.c        (~50 行) — Rule 110 元胞自动机
evaluator/cyclic_tag.c     (~80 行) — cyclic-tag 计算原语
encoder/groundcompiler_encoding.c  (~120 行) — bit ↔ tape 编码
    ↓
manifest_runner: 解析 .ct → 跑 cyclic_tag → 比对 expected
    ↓
manifest assertion PASS/FAIL
```

总信任基 ≈ 250 行 C + 文本 manifest. 人眼可审.

**Ship 标准**:
- 13 FKernel 模块的 `.enum.ct` manifest 全部由 `make -C rule110 test` 验证 (exit 0)
- 0 外部依赖
- 跟 Lean 侧 shorthand 一致 (通过 `lake exe rule110-cross-check` 开发期 sanity check)

**当前状态**: 几乎已 ship. 收尾 = 更新 STATUS.md + tag release.

**Tier A 局限**: 信任 `cyclic_tag.c` 作为 primitive. cyclic tag 比 Rule 110 元胞自动机抽象 (有产生式状态机). 严格意义"完全二进制不接受任何假设"要求衬底是 Rule 110 元胞自动机本身, 那是 Tier B.

### Tier B: Rule 110 物理 witness (严格目标)

**信任路径**:

```
ANSI C 编译器
    ↓
evaluator/rule110.c (~50 行)        — 唯一的 substrate primitive
    ↓
Rule 110 元胞自动机 evolution on .r110 initial pattern
    ↓
decode evolution 结果 → 匹配 .ct 上的 expected
    ↓
manifest assertion PASS/FAIL
```

总信任基 ≈ 50 行 C + Cook 编码协议 + 文本 manifest. `cyclic_tag.c` 退化为 reference implementation, 不在 trust path.

**Ship 标准**:
- 每个 `.enum.ct` 有对应 `.r110`
- Rule 110 evolution 在 `.r110` 上跑出来 decode 后 = `.ct` 对应直接承载输入

**当前状态**: FKernel 直接承载层和 Cook packet 层均已覆盖.

- L3.1 glider A `(f1_1)=111110` phase-exact ✓
- L3.2 collision A-A 直接模拟验证 ✓
- L3.3 leader/ossifier/data_block phase-exact entry points + structural docs ✓
- L3.4 cook_encode interface + composition design ✓
- Martinez 2001/2004 phase catalog 已进入 `encoder/glider_phases.c/h`
- Martinez 2012 collision / soliton table 已进入 `cook_collision_lookup`
- L3.5-L3.7 FKernel `.r110` direct-carrier manifest 生成 + round-trip + smoke test 已接入 `make test`

**Tier B ship 状态**: direct-carrier `.r110` 覆盖 FKernel `.enum.ct` 位串承载; Cook packet composition 覆盖 leader / ossifier / data block phase-exact bodies, 并经 Rule 110 evolution + decoded output window 验证 `.algo.ct` 子集端到端.

---

## 当前状态快照 (Tier A 已 ship — 仅余 tag + 论文引文)

| FKernel 模块 | `.enum.ct` | `.algo.ct` | C 端测试 |
|---|---|---|---|
| Mark | ✓ | n/a | ✓ |
| Hist | ✓ | ✓ bounded | ✓ |
| Ext | ✓ | ✓ bounded | ✓ |
| Sig (SigRel + sameSig) | ✓ | ✓ bounded | ✓ |
| Cont | ✓ | ✓ bounded | ✓ |
| Bundle | ✓ | ✓ bounded | ✓ |
| Unary | ✓ | ✓ bounded | ✓ |
| Ask | ✓ | ✓ bounded | ✓ |
| ExternalBinary | ✓ | ✓ bounded | ✓ |
| Gap | ✓ | ✓ bounded | ✓ |
| Package | ✓ | ✓ bounded | ✓ |
| NameCert | ✓ | ✓ bounded | ✓ |
| Settled | ✓ | ✓ bounded | ✓ |
| GroundCompiler | ✓ (L5.7) | n/a (本身就是 encoding) | ✓ |

`.algo.ct` 全部 bounded 状态. 在新框架下, **universal CT recognizer 不在追求范围** (BEDC 不需要 universal). 已有的 bounded recognizer 是 session 早期 dispatch 产物, 保留不维护.

`make -C rule110 test` exit 0. CI 在 `pr-gate.yml` 已配置 `Rule110 Cross-Check` job.

---

## Tier A 收尾步骤 (剩余 ship 工作)

- [x] T-A.7: tag `rule110-v2.0-fkernel-tier-a` 到 origin at `d3ae91028`
- [x] T-A.8: `papers/bedc/appendices/build_and_verification_log.tex` 引用 Tier A ship state (commit `031c700be`)

**完成 T-A.7 + T-A.8 = Tier A ship 标准达成**.

---

## 数据基础

- `encoder/listPhasesR110.txt`: Martinez 2001 / 2004 Rule 110 phase catalog, 包含 ether、A、B、C1、C2、C3、Ebar、F、G、H 和 glider gun 的 phase strings.
- `encoder/martinez_2012_collisions.txt`: Martinez 2012 Complex Systems 21.2.2 collision / soliton table, 包含 18 个 binary soliton 和 F/Bbar/B collision rows.
- `encoder/glider_phases.c/h`: C99 static const lookup, 当前覆盖 Cook construction 核心使用的 phase strings.
- 参考: Cook 2004; Martinez 2007 arXiv:0706.3348; Martinez, Adamatzky, Chen, Chua 2012, Complex Systems 21.2.2.

## Tier B 推进步骤 (严格目标)

- [x] T-B.1.a: 接入 Martinez 2001/2004 phase catalog 和 Martinez 2012 collision / soliton table
- [x] T-B.1.b: 用 Rule 110 直接模拟验证核心 phase rows 与 collision rows; `tests/test_phase_verifier_martinez.c` 覆盖 9 glider 的 period + displacement, `tests/test_cook_collision_martinez.c` 覆盖 table lookup + 4 collision rows
- [x] T-B.2: 验证 glider B-H phase-exact; B/C/Ebar/F/G/H 已有 canonical lookup, `encoder/cook_glider_D1.c` 与 `encoder/cook_glider_D2.c` emitter 由 `tests/test_cook_glider_D1.c` / `tests/test_cook_glider_D2.c` 覆盖, generic D 保持独立路径
- [x] T-B.3: 实施 leader / ossifier / data_block phase-exact bodies; `tests/test_cook_packet_phase_exact.c` 的 `manual_packet_layout_survives_512_steps` 验证 packet layout
- [x] T-B.4: 实施 `cook_encode_phase_exact()` bodies; `single_production_round_trip_512` 与 `two_productions_round_trip_1024` 验证端到端 round-trip
- [x] T-B.5: 为 FKernel `.enum.ct` 生成对应 `.r110` direct-carrier initial pattern
- [x] T-B.6: round-trip 验证: Rule 110 evolution on `.r110` decode = `.ct` direct-carrier input
- [x] T-B.7: `make test` 覆盖 FKernel `.r110` smoke test 与 Beyond-FKernel appendix 四目录
- [x] T-B.8: 更新 STATUS.md 标 Tier B ship; tag `rule110-v3.0-fkernel-tier-b`
- [x] T-B.9: `.algo.ct` Cook packet round-trip. 22 个 .algo.r110.ct 通过 `make test-algo-r110-semantic` 用真 Rule 110 evolution + cook_decode_output 比对, 全 PASS。`single_production_round_trip_512` / `two_productions_round_trip_1024` 锁定端到端。

**Tier B ship 状态**: `.enum.ct` direct-carrier 子集和 `.algo.ct` Cook packet 子集均在本地验证链路内闭合; Beyond-FKernel appendix 四目录具备 `.r110.ct` 直接承载, 22 个 `.algo.r110.ct` manifest 具备 Rule 110 evolution + decoded output window round-trip.

---

## Lean / L4 / L5 重新定位

### Lean (`lean4/BEDC/FKernel/*`)
- 保留, 0-axiom 0-sorry 状态不动
- **新地位**: 人类可读 shorthand + 论文 bookkeeping
- **不在信任路径**: 任何 Lean kernel bug 不影响 BEDC trust (BEDC trust = Tier A/B 信任路径, 不含 Lean)
- ∀ 陈述读作 "对所有 manifest 列出的具体实例都成立" 的紧凑写法

### L4 cross-check (`rule110/lean-side/Rule110CrossCheck.lean`, `rule110/lean-side/Rule110CrossCheck/**`)
- `lake exe rule110-cross-check` 保留
- `pr-gate.yml` CI 集成保留
- **新地位**: implementation-level sanity check (Lean shorthand 和 rule110 witness 是否一致). 不是 BEDC ship gate.
- L4.3 全 13 enum 族扩展: T-A.1 merge

### L5 Beyond-FKernel mirrors (附录)

已 merge 的 L5.* 产物保留在仓库, 不主动维护, 不参与 ship gate; 四个 manifest 目录均有 `.r110.ct` 直接承载, 并由 `make test` 中的对应 binary 运行:

| 目录 | 对应 Lean | 状态 |
|---|---|---|
| `manifests/topology_up/` | `Derived/TopologyUp` | appendix, `.r110.ct`, `test_topology_up` |
| `manifests/circle_up/` | `Derived/S1Up + ModNUp` | appendix, `.r110.ct`, `test_circle_up` |
| `manifests/fold_up/` | `Derived/FoldMomentKernelUp` | appendix, `.r110.ct`, `test_fold_up` |
| `manifests/meta_cic/` | `MetaCIC` | appendix, `.r110.ct`, `test_meta_cic` |
| `docs/base_reflection_design.md` | `BaseReflection` | design note |

未 merge 的 L5.2 RealUp 和 L5.8 Capstones: 决定**不 merge**, worktree 清理.

未来如果 BEDC scope 扩展到某个 Derived 模块, 这些附录可上升到主线 (需要补 cross-check + CI gate).

---

## 显式 Out-of-Scope

下列项**不追求**, 不在路线图待办里:

- ❌ Universal CT recognizers (BEDC 不需要 universal — 是 CIC sugar). 已有 12 个 bounded 保留, 不维护
- ❌ CIC-in-rule110 实现 (会重新引入 CIC 元理论信任, 信任基反而变大)
- ❌ BaseReflection rule110 manifest implementation (research-open, 不需要)
- ❌ MetaCIC universal (同上)
- ❌ Beyond-FKernel modules 的 formal closure 主张 (Derived/* 不在 BEDC kernel)
- ❌ L2.1 BHist universal CT recognizer (不需要)

---

## 历史

- M2 (2026-05): Cook construction 行为脚手架 — 归档至 `history/ROADMAP-m2-cook-construction.md`
- M3 (2026-05): 13 FKernel 模块 `.enum.ct` 全套 + bounded `.algo.ct` — 归档至 `history/ROADMAP-m3-fkernel-modules.md`
- 2026-05-12 早期: master roadmap v1 (含 Level 5/6 整树双 substrate), 由对话推动
- 2026-05-12 晚期: master roadmap v2 (FKernel + GroundCompiler scope, Tier 概念未引入)
- 2026-05-13: 本路线图 v3. BEDC 重定位为 "finite witness, Lean kernel 不在 trust path"; 双 tier 架构

---

## 给 codex worker 的指令 (autonomous progression)

任何后续 codex CLI worker 在 rule110 trunk 上推进时:

1. **Tier A ship 优先**: T-A.1 ~ T-A.8 是当前 critical path
2. **Tier B 工程推进**: 使用 Martinez catalog 和 collision table 推进 T-B.*, 每步需保留直接模拟验证
3. **不追求 universal / CIC-in-rule110**: 显式 out-of-scope
4. **附录不动**: `manifests/topology_up|circle_up|fold_up|meta_cic/` 不主动改
5. **每个 commit 自洽**: `make -C rule110 test` PASS + 0 axiom + cross-check PASS
6. **merge 不 rebase**: 永远 push 不 force; 单 commit 原子
