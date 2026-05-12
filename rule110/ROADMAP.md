# rule110 路线图

**项目**: BEDC 基于 Rule 110 元胞自动机 + 循环标签系统的最小信任 substrate.
**分支**: `rule110` (单 trunk; 历史里程碑 m2/m3 已归档到 `history/`).
**姊妹**: `lean4/BEDC/` (Lean 4 形式化), `papers/bedc/` (LaTeX 论文).
**硬约束**: 零外部依赖, ANSI C99, Rule 110 + 循环标签系统作为唯二 substrate 原语.

---

## 最终目标

**FKernel + GroundCompiler 在 Lean 和 rule110 双 substrate 上 CI 强制一致.**

具体含义:

- `lean4/BEDC/FKernel/` 13 个模块 (Mark / Hist / Ext / Sig / Cont / Bundle / Unary / Ask / ExternalBinary / Gap / Package / NameCert / Settled) 加 `lean4/BEDC/GroundCompiler/ChannelEncoding.lean` 的所有闭项定理
- 在 rule110 substrate 上有对应的 `.enum.ct` / `.algo.ct` manifest
- `lake exe rule110-cross-check` 全部 PASS, 退出 0
- `python3 tools/check-axioms.py` 全程 0 axiom
- `pr-gate.yml` CI 强制: 任何 FKernel 或 GroundCompiler 改动必须双 substrate 同步通过才能合并

**不在 scope 内**: `lean4/BEDC/Derived/**`, `lean4/BEDC/BaseReflection/**`, `lean4/BEDC/MetaCIC/**`, `lean4/BEDC/Capstone/**`. 这些可以在 Lean 侧单 substrate 自由演进; rule110 侧若已有的 exploratory mirror 保留, 但不参与 CI gate (见末尾附录).

这个目标是**有界、可达成**的, 不是开放式无限工作.

---

## 当前状态快照

| 模块 | `.enum.ct` (闭项) | `.algo.ct` (通用 recognizer) | Lean cross-check |
|---|---|---|---|
| Mark | ✓ done | n/a (recognition 平凡) | ✓ done |
| Hist | ✓ done | `[!]` bounded (L2.1 defer) | ✓ done |
| Ext | ✓ done | `[!]` bounded | ✓ done |
| Sig (SigRel + sameSig) | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| Cont | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| Bundle | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| Unary | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| Ask | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| ExternalBinary | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| Gap | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| Package | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| NameCert | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| Settled | ✓ done | `[!]` bounded | 待 merge (L4.3) |
| GroundCompiler | 待加 (L5.7 在跑) | n/a (encoding 自身) | 待加 (随 L5.7) |

`[!]` 含义: bounded positional-certificate CTS 覆盖代表性 fixtures + 浅深度 sweep; 通用 CT recognizer 工程量级别大, 已在 `docs/<module>_algo_design.md` 记录所需算法.

**substrate 侧基础设施**: `evaluator/rule110.c` (~50 LOC) + `evaluator/cyclic_tag.c` (~80 LOC) + `encoder/groundcompiler_encoding.c` (~120 LOC) + manifest runner + 14 test 二进制. `make test` 全过.

**Lean 侧基础设施**: `lake exe rule110-cross-check` 已成 Lake exe target, 当前覆盖 3 enum 族 (mark/hist/ext), L4.3 扩展到全 13 族待 merge.

**CI**: `.github/workflows/pr-gate.yml` 已有 `rule110-cross-check` job, 结构化 FAIL 消息 5 类区分, runtime budget 已记录.

---

## 主线四轴

新路线图按 4 个正交轴组织, 替代之前的 "Level" 编号.

### 轴 A: rule110 substrate 见证

- A.1: 13 FKernel 模块 + GroundCompiler 各自有 `.enum.ct` (闭项 enumeration)
  - 状态: 13/14 done; GroundCompiler 待 L5.7 merge
- A.2: 同一组模块各自有 `.algo.ct` (通用 recognizer 或 bounded CTS + obstruction doc)
  - 状态: 12/12 FKernel 已 bounded `[!]` ship 状态; L2.1 BHist universal 显式 defer
  - 任何 `.algo.ct` 要 ship "universal" 需 ~1 月以上 CT 工程量, 不在主线必经路径
- A.3: `make test` exit 0 不变

### 轴 B: Lean ↔ rule110 cross-check

- B.1: `lean4/scripts/rule110_cross_check.lean` 解析每个 `.enum.ct`, 调用对应 `BEDC.FKernel.<Module>` 闭项定理, 报 PASS/FAIL
  - 状态: 3 enum 族 done (mark/hist/ext); 10 族 (sig/cont/bundle/unary/ask/extbin/gap/package/namecert/settled) 待 merge (L4.3, conflict 待解)
- B.2: `lake exe rule110-cross-check` 默认参数覆盖所有 14 个 manifest 族 (含 GroundCompiler)
  - 状态: `lakefile.lean` 已注册 exe; 默认参数当前 3 族, 随 L4.3 merge 扩到 13, 随 L5.7 merge 扩到 14
- B.3: 失败消息分类 (C-decode / Lean-decode / semantic-mismatch / missing-target / fixture-incomplete) — done
- B.4: 0 axiom 全程 — done

### 轴 C: CI ship gate

- C.1: `pr-gate.yml` 在 `rule110/**` 或 `lean4/BEDC/FKernel/**` 或 `lean4/scripts/rule110_cross_check*` 改动时触发
  - 状态: workflow yaml 已加, 实际触发条件待验证
- C.2: CI 跑序列: `make -C rule110 test` → `lake build BEDC.FKernel.*` → `lake exe rule110-cross-check` → `python3 tools/check-axioms.py`
  - 状态: workflow 已有, 待 L4.3 merge 后端到端跑一次确认
- C.3: 合并条件 (branch protection): 上述全部 PASS 才能 merge 到 rule110 trunk
  - 状态: 未配置 GitHub branch protection rules (当前是人工纪律 + CI 状态)

### 轴 D: Cook 物理嵌入 (stretch, 阻塞)

**这一轴不是 ship-blocking**. Cook 2004 phase-exact glider B-H catalog 公开二手源不一致, 直接图访问受限. 已尽量推进:

- D.1: Glider A `(f1_1)=111110` phase-exact + 周期-3 / 位移-2 验证 — done
- D.2: Glider B-H phase-exact — **blocked** 等 Cook 2004 figure 直接访问或可信机读 catalog
- D.3: Collision lookup table: A-A 验证 done; 其他 heuristic pending D.2
- D.4: Leader / ossifier / data_block: phase-exact entry points + structural docs done; bodies blocked on D.2
- D.5: `cook_encode_phase_exact()` interface + composition design — L3.4 worker 在跑
- D.6: `.r110` manifest 全 44 族 + round-trip 验证 — 全 blocked on D.2

Cook 阻塞**不影响最终目标达成**. 最终目标只需要 substrate manifest + Lean cross-check + CI gate; 物理嵌入是雄心目标, 等外部资源.

---

## 阶段划分

按推进顺序排.

### 阶段 0: substrate scaffold + bounded recognizer 全集 + 设计文档

**完成态**. 现在的状态.

### 阶段 1: 闭合 FKernel cross-check

- [ ] 1.1: merge `loop-L4-3-expansion` (10 enum 族扩展; 当前与 L4.4 有 7 处 lean script conflict 待解)
- [ ] 1.2: 等 `loop-L5-7-groundcompiler` 跑完 + merge (GroundCompiler manifest + cross-check 注册)
- [ ] 1.3: 本地全套验证: `make -C rule110 test`, `lake build BEDC.FKernel.*`, `lake exe rule110-cross-check`, `python3 tools/check-axioms.py` 全 exit 0
- [ ] 1.4: push 到 `origin/rule110`

### 阶段 2: CI ship gate 端到端验证

- [ ] 2.1: 在 PR 上故意制造 FKernel 不一致 (临时把某个 enum manifest 的 expected 改错), 确认 `pr-gate.yml` FAIL
- [ ] 2.2: 还原, 确认 `pr-gate.yml` PASS
- [ ] 2.3: 配置 GitHub branch protection: `rule110` trunk require pr-gate status check
- [ ] 2.4: 更新 `rule110/docs/cross_check.md` 写明 CI 强制路径

### 阶段 3: ship signal (释放 tag)

- [ ] 3.1: 更新 `rule110/STATUS.md` 反映 FKernel 双 substrate 闭合状态
- [ ] 3.2: tag `rule110-v2.0-fkernel-bisubstrate` 到 origin
- [ ] 3.3: 论文 `papers/bedc/` 引用最终 commit hash + 包含 `rule110-cross-check` 状态作为外部见证

**完成阶段 1 + 2 + 3 即达成最终目标**. 预估总工作量 1-3 天 (主要是 1.1 conflict 解决 + 1.2 等 worker + 2.1-2.4 CI 验证).

### 阶段 4 (可选, 雄心): 提升某些 `[!]` 到 universal

任何一个 `[!]` 模块的 universal CT recognizer 工程量都 ~1 月+. 选择性推进, 不阻塞 ship.

最高 ROI 候选:

- L2.1 BHist universal — 解锁后 Package 也跟着 universal 化 (Package 依赖 hsame)
- L2.6 Unary universal — 算法相对简单, ~5-10 productions

### 阶段 5 (可选, 雄心): Cook D 轴推进

需要外部资源 (Cook 2004 figure 直接访问或机读 catalog). 不阻塞 ship.

---

## 验收标准

```bash
# 全部 exit 0 即达成最终目标
cd /Users/auric/newmath/rule110 && make clean && make && make test
cd /Users/auric/newmath/lean4 && lake build \
    BEDC.FKernel.Mark BEDC.FKernel.Hist BEDC.FKernel.Ext \
    BEDC.FKernel.Sig BEDC.FKernel.Cont BEDC.FKernel.Bundle \
    BEDC.FKernel.Unary BEDC.FKernel.Ask BEDC.FKernel.ExternalBinary \
    BEDC.FKernel.Gap BEDC.FKernel.Package BEDC.FKernel.NameCert \
    BEDC.FKernel.Settled BEDC.GroundCompiler.ChannelEncoding
cd /Users/auric/newmath/lean4 && lake exe rule110-cross-check
cd /Users/auric/newmath && python3 tools/check-axioms.py
```

CI 侧: `pr-gate.yml` 对 `rule110/**` 或 `lean4/BEDC/FKernel/**` 或 `lean4/scripts/rule110_cross_check*` 任何 PR 都跑上述序列, 全 PASS 才允许 merge.

---

## 附录: Beyond-FKernel exploratory mirrors

以下 rule110 manifest 目录由历史 dispatch 产生, **不在 FKernel scope, 不参与 CI gate, 不是路线图主线**. 保留作为独立见证 / future research 起点:

| 目录 | 对应 Lean | 状态 | 备注 |
|---|---|---|---|
| `manifests/topology_up/` | `Derived/TopologyUp` | 3 enum manifests + test | exploratory |
| `manifests/circle_up/` | `Derived/S1Up + ModNUp` | 3 enum manifests + test | exploratory |
| `manifests/fold_up/` | `Derived/FoldMomentKernelUp` | 3 enum manifests + test | exploratory |
| `manifests/meta_cic/` | `MetaCIC` | 3 enum manifests + test | exploratory |
| `docs/base_reflection_design.md` | `BaseReflection` | design-only doc | 研究开放 |

如果未来 BEDC scope 扩展到包含某个 Derived 模块, 这些 mirror 可以从附录上升到主线; 上升时需补 `.algo.ct` + cross-check 注册 + CI gate.

`manifests/real_up/` (L5.2) 和 `manifests/capstones/` (L5.8) 当前为 worker 已 finish 或在跑 但未 merge 状态, 待用户决定纳入附录或放弃.

---

## 历史

- M2 (2026-05): Cook construction 行为脚手架 (ether + 8 gliders + leader/ossifier/data_block + cook_encode 行为版) — 归档至 `history/ROADMAP-m2-cook-construction.md`
- M3 (2026-05): 13 FKernel 模块的 `.enum.ct` 全套 + bounded `.algo.ct` — 归档至 `history/ROADMAP-m3-fkernel-modules.md`
- 2026-05-12: master roadmap 第一版 (含 Level 5 + Level 6), 由对话推动, 现已替换为此 FKernel-scoped 版本
- 2026-05-13: 本路线图. Beyond-FKernel 的 L5.* 工作产物移入附录, 不进 CI gate

---

## 给 codex worker 的指令 (autonomous progression)

任何后续 codex CLI worker 在 rule110 trunk 上推进时:

1. **只关心 scope 内任务**: FKernel 13 模块 + GroundCompiler. Beyond-FKernel 不主动推进 (除非用户显式 scope 扩展)
2. **优先阶段 1 + 2 + 3**: 闭合 FKernel cross-check → CI 强制 → release tag
3. **不动 Cook D 轴**: 除非用户明确指示且提供 Cook figure 资料
4. **每个 commit 自洽**: substrate `make test` PASS + cross-check PASS + 0 axiom
5. **不动附录 manifests**: `topology_up/` / `circle_up/` / `fold_up/` / `meta_cic/` 是 exploratory, 不主动改
6. **永远 push 不 force**: merge 不 rebase, 单 commit 原子
