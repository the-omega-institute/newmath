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
- Rule 110 evolution 在 `.r110` 上跑出来 decode 后 = `.ct` 跑出来

**当前状态**: 部分推进, 关键 blocked.

- L3.1 glider A `(f1_1)=111110` phase-exact ✓
- L3.2 collision A-A 直接模拟验证 ✓
- L3.3 leader/ossifier/data_block phase-exact entry points + structural docs ✓ (bodies blocked)
- L3.4 cook_encode interface + composition design ✓
- **L3.1 B-H gliders blocked on Cook 2004 figure access**
- L3.5-L3.7 (.r110 manifest 生成 + round-trip + smoke test) 全 blocked

**ship blocker**: Cook 2004 phase-exact catalog. 公开二手源不一致, 需要直接图访问或可信机读 catalog. 解锁后预估 4-8 周可完成全集.

否则 Tier B **无限期 blocked**, 长期目标方向不变.

---

## 当前状态快照 (Tier A 接近 ship)

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

## Tier A 收尾步骤 (近期 ship 路径)

- [ ] T-A.1: merge `loop-L4-3-expansion` (10 enum 族 cross-check; 当前与 L4.4 有 7 处 lean script conflict, 解 conflict 后 merge). L4 cross-check 是开发期工具, **不是 BEDC trust** — 仍然 merge 但语义降级
- [ ] T-A.2: merge `loop-L5-7-groundcompiler` (GroundCompiler manifest, in-scope encoding primitive)
- [ ] T-A.3: merge `loop-L3-4-cook-encoder` (Tier B 推进, `cook_encode_phase_exact()` interface)
- [ ] T-A.4: 本地全套验证: `make -C rule110 test`, `lake build BEDC.FKernel.*`, `lake exe rule110-cross-check`, `python3 tools/check-axioms.py` 全 exit 0
- [ ] T-A.5: 更新 `rule110/STATUS.md` 反映 Tier A ship 状态
- [ ] T-A.6: push 到 `origin/rule110`, 等 CI 全绿
- [ ] T-A.7: tag `rule110-v2.0-fkernel-tier-a` 到 origin
- [ ] T-A.8: 在 `papers/bedc/` 引用最终 commit hash 作为 BEDC 引文外部见证

**完成 T-A.* 全部 = Tier A ship 标准达成**. 预估 1-3 天.

---

## Tier B 推进步骤 (严格目标, blocked)

- [ ] T-B.1: 获取 Cook 2004 figure 直接访问 (paper 复印 / 扫描 / 可信二手 catalog)
- [ ] T-B.2: 验证 glider B-H phase-exact (每个 ~1 天)
- [ ] T-B.3: 实施 leader / ossifier / data_block phase-exact bodies (依赖 T-B.2)
- [ ] T-B.4: 实施 `cook_encode_phase_exact()` bodies (依赖 T-B.3)
- [ ] T-B.5: 为每个 `.enum.ct` 生成对应 `.r110` initial pattern
- [ ] T-B.6: round-trip 验证: Rule 110 evolution on `.r110` decode = `.ct` execution
- [ ] T-B.7: `make test` 扩到 `.r110` smoke test 全 44 族
- [ ] T-B.8: 更新 STATUS.md 标 Tier B ship; tag `rule110-v3.0-fkernel-tier-b`

**预估**: 4-8 周 IF T-B.1 解锁; 否则**无限期 blocked**.

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

已 merge 的 L5.* 产物保留在仓库, 不主动维护, 不参与 ship gate:

| 目录 | 对应 Lean | 状态 |
|---|---|---|
| `manifests/topology_up/` | `Derived/TopologyUp` | merged, exploratory |
| `manifests/circle_up/` | `Derived/S1Up + ModNUp` | merged, exploratory |
| `manifests/fold_up/` | `Derived/FoldMomentKernelUp` | merged, exploratory |
| `manifests/meta_cic/` | `MetaCIC` | merged, exploratory |
| `docs/base_reflection_design.md` | `BaseReflection` | merged, design-only |

未 merge 的 L5.2 RealUp 和 L5.8 Capstones: 决定**不 merge**, worktree 清理.

未来如果 BEDC scope 扩展到某个 Derived 模块, 这些附录可上升到主线 (需要补 .r110 + cross-check + CI gate).

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
2. **Tier B 等外部资源**: 不主动推进 T-B.* 除非用户提供 Cook figure 资料
3. **不追求 universal / CIC-in-rule110**: 显式 out-of-scope
4. **附录不动**: `manifests/topology_up|circle_up|fold_up|meta_cic/` 不主动改
5. **每个 commit 自洽**: `make -C rule110 test` PASS + 0 axiom + cross-check PASS
6. **merge 不 rebase**: 永远 push 不 force; 单 commit 原子
