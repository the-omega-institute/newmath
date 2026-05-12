# rule110 路线图重写实施计划

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 把 `rule110/ROADMAP.md` 改写为 Tier A/Tier B 双层框架, 反映"BEDC = finite witness, Lean kernel 不在 trust path" 的新定位; 同时处理 5 个待 merge worker (3 in-scope merge + 2 out-of-scope discard) 并更新 `STATUS.md`.

**Architecture:** 单 file 重写 (`ROADMAP.md`) + 1 file 更新 (`STATUS.md`) + 5 个 worktree 处理. 没有新代码, 全部是 docs + git 操作.

**Tech Stack:** Markdown, git worktree, git merge, gh CLI (CI 验证).

**前序设计**: `docs/superpowers/specs/2026-05-13-rule110-roadmap-rewrite-design.md`

---

## 文件结构

| 文件 | 操作 | 说明 |
|---|---|---|
| `rule110/ROADMAP.md` | 完全重写 | 当前 203 行 (FKernel-only v2 版); 新版本按 Tier A/B 重组, 预估 ~200 行 |
| `rule110/STATUS.md` | 局部更新 | 反映 Tier A 当前 ship 状态; 不动 LOC/manifest 数 |
| `rule110/README.md` | 可选小更新 | 第一段加一行说明双 tier 框架 (surgical) |

| Worktree | 操作 | 理由 |
|---|---|---|
| `/tmp/wt-L4-3-expansion` | merge, 解 7 处 conflict | in-scope: L4 cross-check 全 13 族; 新框架降级为开发期工具, 仍然 merge |
| `/tmp/wt-L5-7-groundcompiler` | merge | in-scope: GroundCompiler 是 encoding primitive, 在新 scope 内 |
| `/tmp/wt-L3-4-cook-encoder` | merge | in-scope: Tier B 工作 (cook_encode interface), 推进 Tier B |
| `/tmp/wt-L5-2-realup` | 删除, 不 merge | out-of-scope: Derived/RealUp, 新 scope 不包含 |
| `/tmp/wt-L5-8-capstones` | 删除, 不 merge | out-of-scope: Capstone, 新 scope 不包含 |

---

## Task 1: 写新 ROADMAP.md

**Files:**
- Modify (完全替换): `rule110/ROADMAP.md`

**前置**: 已 commit `7f17344a8` (rule110 trunk 上). 直接 working tree 改.

- [ ] **Step 1.1: 在工作目录写新 ROADMAP.md 内容**

用 Write 工具完全替换 `rule110/ROADMAP.md`. 新内容如下 (完整, ~200 行):

```markdown
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

### L4 cross-check (`lean4/scripts/rule110_cross_check.lean`)
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
```

- [ ] **Step 1.2: 验证 ROADMAP.md 格式**

Run: `wc -l rule110/ROADMAP.md`
Expected: 约 180-220 行 (在 800 行单文件上限内)

Run: `grep -c '^## ' rule110/ROADMAP.md`
Expected: 至少 8 (主章节: 核心原则, 双 Tier, 当前状态, Tier A 收尾, Tier B 推进, Lean/L4/L5, out-of-scope, 历史, codex 指令)

- [ ] **Step 1.3: commit**

```bash
cd /Users/auric/newmath
git add rule110/ROADMAP.md
git commit -m "$(cat <<'EOF'
rule110 路线图 v3: Tier A/B 框架, BEDC = finite witness, Lean kernel 不在 trust path

详细设计见 docs/superpowers/specs/2026-05-13-rule110-roadmap-rewrite-design.md.

关键变化:
- 核心原则: BEDC ontology 是有限可观察, Lean ∀ 是 shorthand 不是本征
- 信任路径反转: rule110 主, Lean shorthand
- 双 tier:
  - Tier A cyclic-tag witness (1-3 天 ship)
  - Tier B Rule 110 物理 witness (4-8 周 IF Cook figure 解锁; 否则 blocked)
- Universal CT recognizer / CIC-in-rule110 显式 out-of-scope (BEDC 不需要)
- L4 cross-check 降级为开发期工具, 不再是 ship gate
- L5 Beyond-FKernel mirrors 保留为附录
EOF
)"
```

Expected: 1 commit, 路线图重写

---

## Task 2: 更新 STATUS.md (反映 Tier A 状态)

**Files:**
- Modify: `rule110/STATUS.md`

- [ ] **Step 2.1: 读 STATUS.md 当前内容**

Run: `head -50 rule110/STATUS.md`

观察当前的 status snapshot section 在哪些行.

- [ ] **Step 2.2: 加 Tier A 状态段**

在 STATUS.md 顶部 "Project status snapshot" 之后, 插入新 section. 用 Edit 工具加:

```markdown
## 框架 (2026-05-13 路线图 v3 之后)

详细见 `ROADMAP.md`. 简要:

- **当前状态**: Tier A (cyclic-tag witness) 接近 ship. 信任基 ≈ 250 行 C + 文本 manifest, Lean kernel 不在 trust path.
- **下一步**: T-A.1~T-A.8 收尾, 预估 1-3 天.
- **严格目标 (Tier B)**: Rule 110 物理 witness via Cook construction, blocked on Cook 2004 figure access.

L4 cross-check / L5 Beyond-FKernel mirrors 重新定位为开发工具 / 附录, 见 ROADMAP §"Lean / L4 / L5 重新定位".
```

- [ ] **Step 2.3: commit**

```bash
git add rule110/STATUS.md
git commit -m "STATUS: 加 Tier A 框架段, 链接到新 ROADMAP v3"
```

---

## Task 3: Merge L4.3 expansion (解 7 处 lean script conflict)

**Files:**
- Merge from: `/tmp/wt-L4-3-expansion` (branch `loop-L4-3-expansion`)
- Conflicts expected: `lean4/scripts/rule110_cross_check.lean` (7 处), `lean4/scripts/rule110_cross_check_README.md` (auto-merging OK)

**前置**: L4.4 已经把 `rule110_cross_check.lean` 改成了 5-类结构化 FAIL 消息. L4.3 worker 把它扩展到 10 enum 族. 两者改了同一段代码.

- [ ] **Step 3.1: 启动 merge**

```bash
cd /Users/auric/newmath
git merge --no-ff loop-L4-3-expansion -m "merge: loop-L4-3-expansion (L4 cross-check 全 13 enum 族 — 开发期工具)"
```

Expected: 7 处 conflict in `lean4/scripts/rule110_cross_check.lean`, README 也有 conflict 但 auto-merge.

- [ ] **Step 3.2: 检查 conflict 位置**

```bash
grep -n '^<<<<<<<\|^>>>>>>>' lean4/scripts/rule110_cross_check.lean
```

Expected: 14 行号 (7 conflict, 各 2 markers `<<<` + `>>>>`).

- [ ] **Step 3.3: 逐个解 conflict**

策略: **保留 L4.3 worker 的扩展** (新 10 enum 族支持) + **加上 L4.4 的 5 类 FAIL 消息分类**.

对每个 conflict block:
1. 读 HEAD 版本 (L4.4 改动)
2. 读 loop-L4-3-expansion 版本 (新族 dispatch)
3. 合并: 保留 L4.3 的新族注册 + L4.4 的 FAIL 分类

具体每个 conflict 的合并参考 L4.3 worker 输出的 `lean4/scripts/rule110_cross_check.lean` 文件 (1499 行) 跟 L4.4 当前在 trunk 上版本对比. 用 git 三方 merge view:

```bash
git diff --base lean4/scripts/rule110_cross_check.lean | head -200
```

逐个 conflict 应用以下 pattern:
- 若 conflict 是新族 dispatch (case `family = "sig"` 等): 取 loop-L4-3-expansion 版本
- 若 conflict 是 FAIL kind 区分 (例如 `FAIL kind=C-decode`): 取 HEAD 版本
- 若 conflict 同时涉及两者: 手工拼合, 把新族用 FAIL kind 包起来

用 Edit 工具每次解一个 conflict, 确保 git markers 都清除.

- [ ] **Step 3.4: 验证文件无 conflict markers**

```bash
grep -c '^<<<<<<<\|^=======$\|^>>>>>>>' lean4/scripts/rule110_cross_check.lean
```

Expected: 0

- [ ] **Step 3.5: build + 运行**

```bash
cd /Users/auric/newmath/lean4
lake build BEDC.FKernel.Mark BEDC.FKernel.Hist BEDC.FKernel.Ext BEDC.FKernel.Sig BEDC.FKernel.Cont BEDC.FKernel.Bundle BEDC.FKernel.Unary BEDC.FKernel.Ask BEDC.FKernel.ExternalBinary BEDC.FKernel.Gap BEDC.FKernel.Package BEDC.FKernel.NameCert BEDC.FKernel.Settled
```

Expected: build 成功.

```bash
lake build rule110-cross-check && lake exe rule110-cross-check
```

Expected: 全部 PASS, exit 0. 输出含 mark/hist/ext + sig/cont/bundle/unary/ask/extbin/gap/package/namecert/settled 各族 PASS line.

- [ ] **Step 3.6: 完成 merge commit**

```bash
cd /Users/auric/newmath
git add lean4/scripts/rule110_cross_check.lean lean4/scripts/rule110_cross_check_README.md rule110/ROADMAP.md
git commit  # 用默认 merge message, 之前 step 3.1 已经给过
```

如果 merge --no-ff 自动产生的 commit 没有, 重新 commit:
```bash
git commit -m "merge: loop-L4-3-expansion (L4 cross-check 全 13 enum 族 — 开发期工具)"
```

- [ ] **Step 3.7: 清理 worktree + branch**

```bash
git worktree remove /tmp/wt-L4-3-expansion
git branch -D loop-L4-3-expansion
```

---

## Task 4: Merge L5.7 GroundCompiler (in-scope)

**Files:**
- Merge from: `/tmp/wt-L5-7-groundcompiler` (branch `loop-L5-7-groundcompiler`)
- Conflicts expected: `rule110/ROADMAP.md` (主), `rule110/Makefile` (可能)

- [ ] **Step 4.1: 启动 merge**

```bash
cd /Users/auric/newmath
git merge --no-ff loop-L5-7-groundcompiler -m "merge: loop-L5-7-groundcompiler (L5.7 GroundCompiler manifest — encoding primitive in-scope)"
```

Expected: ROADMAP.md conflict (因为 Task 1 重写了 ROADMAP).

- [ ] **Step 4.2: 解 ROADMAP conflict**

ROADMAP.md 的 conflict 都在 §"当前状态快照" 表格行. 我们新 ROADMAP 表格已经包含了 `GroundCompiler | ✓ (L5.7) | n/a | ✓` 行, 所以直接**保留 HEAD 版本** (新 ROADMAP), 丢弃 worker 版本.

用 Edit 工具去掉 ROADMAP.md 里所有 `<<<<<<<` / `=======` / `>>>>>>>` markers, 保留 HEAD content.

```bash
grep -c '^<<<<<<<' rule110/ROADMAP.md
```

Expected: 0

- [ ] **Step 4.3: 如果 Makefile 也 conflict, 同样处理**

```bash
git status -s | grep '^UU'
```

如果有 Makefile UU:
- 读 conflict (`grep -n '^<<<<<<<' rule110/Makefile`)
- L5.7 加了 `tests/test_ground_compiler` 到 TESTS 列表 + 一个 per-test rule
- 保留 HEAD 然后**手工把 L5.7 的两段加进去** (worker 版本一定有的)

具体 Edit 调用根据 conflict 内容:
- TESTS 列表加 `$(TEST_DIR)/test_ground_compiler`
- 加 per-test rule:
```makefile
$(TEST_DIR)/test_ground_compiler: $(TEST_DIR)/test_ground_compiler.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_ground_compiler.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c
```

- [ ] **Step 4.4: 验证 build + test**

```bash
cd /Users/auric/newmath
make -C rule110 clean
make -C rule110
make -C rule110 tests/test_ground_compiler
./rule110/tests/test_ground_compiler
make -C rule110 test
```

Expected:
- build 成功
- `./tests/test_ground_compiler` PASS
- `make test` 全 PASS, exit 0

- [ ] **Step 4.5: 完成 merge + 清理**

```bash
git add rule110/ROADMAP.md rule110/Makefile
git commit  # 默认 merge message; 若需要重 commit:
# git commit -m "merge: loop-L5-7-groundcompiler (L5.7 GroundCompiler manifest — encoding primitive in-scope)"
git worktree remove /tmp/wt-L5-7-groundcompiler
git branch -D loop-L5-7-groundcompiler
```

---

## Task 5: Merge L3.4 Cook encoder (Tier B 工作)

**Files:**
- Merge from: `/tmp/wt-L3-4-cook-encoder` (branch `loop-L3-4-cook-encoder`)
- Conflicts expected: `rule110/ROADMAP.md` (主), 可能 `rule110/encoder/cook_encode.{c,h}` 也涉及

- [ ] **Step 5.1: 启动 merge**

```bash
git merge --no-ff loop-L3-4-cook-encoder -m "merge: loop-L3-4-cook-encoder (L3.4 cook_encode_phase_exact interface + composition design — Tier B 推进)"
```

- [ ] **Step 5.2: 解 ROADMAP conflict**

跟 Task 4.2 类似: 保留新 ROADMAP HEAD 版本, 丢弃 worker 改动 (worker 改的是旧 ROADMAP, 新 ROADMAP 已经把 L3.* 写在 Tier B 推进步骤了).

- [ ] **Step 5.3: 如果 cook_encode.c/h 有 conflict, 解开**

```bash
git status -s | grep '^UU'
```

若 cook_encode.{c,h} UU:
- worker 加了 `cook_encode_phase_exact()` 函数, header 加了 declaration
- HEAD 上没动这两个文件
- **保留 worker 版本** (worker 内容是新增 function, 不冲突业务逻辑)

用 Edit 工具消 markers.

- [ ] **Step 5.4: 验证 build + test**

```bash
make -C rule110 clean
make -C rule110
make -C rule110 test
```

Expected: 全 PASS, exit 0.

- [ ] **Step 5.5: 完成 merge + 清理**

```bash
git add rule110/
git commit  # 默认 merge message
git worktree remove /tmp/wt-L3-4-cook-encoder
git branch -D loop-L3-4-cook-encoder
```

---

## Task 6: 放弃 out-of-scope worktrees (L5.2 + L5.8)

**Files:**
- Remove: `/tmp/wt-L5-2-realup` (branch `loop-L5-2-realup`)
- Remove: `/tmp/wt-L5-8-capstones` (branch `loop-L5-8-capstones`)

**理由**: 新 scope 不包含 Derived/RealUp 和 Capstone. worker 产物虽然 finish 但不进 trunk.

- [ ] **Step 6.1: 删除 L5.2 RealUp worktree + branch**

```bash
cd /Users/auric/newmath
git worktree remove /tmp/wt-L5-2-realup
git branch -D loop-L5-2-realup
```

Expected: worktree 移除, branch 删除. work in commit `cc471df00` 仍在 git reflog 里可恢复 (30 天).

- [ ] **Step 6.2: 删除 L5.8 Capstones worktree + branch**

```bash
git worktree remove /tmp/wt-L5-8-capstones
git branch -D loop-L5-8-capstones
```

- [ ] **Step 6.3: 验证 worktree 列表清空**

```bash
git worktree list
```

Expected: 只剩 `/Users/auric/newmath` 主 worktree.

```bash
git branch | grep 'loop-'
```

Expected: 空 (没有 `loop-*` branches 留存).

---

## Task 7: 全套验证 + push

**Files:**
- 验证: 整个仓库

- [ ] **Step 7.1: substrate 测试**

```bash
cd /Users/auric/newmath
make -C rule110 clean
make -C rule110 test 2>&1 | tail -3
```

Expected:
```
ALL TESTS PASSED
```
exit 0.

- [ ] **Step 7.2: Lean build**

```bash
cd /Users/auric/newmath/lean4
lake build BEDC.FKernel.Mark BEDC.FKernel.Hist BEDC.FKernel.Ext BEDC.FKernel.Sig BEDC.FKernel.Cont BEDC.FKernel.Bundle BEDC.FKernel.Unary BEDC.FKernel.Ask BEDC.FKernel.ExternalBinary BEDC.FKernel.Gap BEDC.FKernel.Package BEDC.FKernel.NameCert BEDC.FKernel.Settled BEDC.GroundCompiler.ChannelEncoding
```

Expected: build 成功, 无 warning 上升为 error.

- [ ] **Step 7.3: cross-check 全族跑通**

```bash
cd /Users/auric/newmath/lean4
lake build rule110-cross-check
lake exe rule110-cross-check
```

Expected: 输出 mark / hist / ext / sig / cont / bundle / unary / ask / extbin / gap / package / namecert / settled 各族 PASS 行. exit 0.

- [ ] **Step 7.4: axiom audit**

```bash
cd /Users/auric/newmath
python3 tools/check-axioms.py
```

Expected: `Axiom audit: 0 axioms in lean4/BEDC/. Project invariant holds.`

- [ ] **Step 7.5: 检查 codex-auto-dev 活跃度**

```bash
gh run list --branch codex-auto-dev --limit 5
```

Expected: 没有大量 in-progress run; 安全 push 窗口.

- [ ] **Step 7.6: push**

```bash
cd /Users/auric/newmath
git log --oneline -7
git push origin rule110
```

Expected: push 成功. 远程 SHA 推进.

- [ ] **Step 7.7: 后台 watch CI**

```bash
gh run list --branch rule110 --limit 1
# 拿到 run ID, 然后:
# gh run watch <id> --exit-status > /tmp/pr-ci.log 2>&1 &
# 或者用 Bash run_in_background: true
```

不阻塞等. CI 完成 task-notification 唤回.

CI 应该 PASS:
- Detect relevant changes
- PDF / Build main.pdf
- Lean4 / Build Lean4
- Rule110 Cross-Check (test_rule110 fmemopen 修已 land, L4.3 全族扩展也已 merge)
- Gate

---

## 验收标准 (整个 plan 完成时)

```bash
# 所有以下命令 exit 0:
cd /Users/auric/newmath/rule110 && make clean && make && make test
cd /Users/auric/newmath/lean4 && lake build BEDC.FKernel.Mark BEDC.FKernel.Hist BEDC.FKernel.Ext BEDC.FKernel.Sig BEDC.FKernel.Cont BEDC.FKernel.Bundle BEDC.FKernel.Unary BEDC.FKernel.Ask BEDC.FKernel.ExternalBinary BEDC.FKernel.Gap BEDC.FKernel.Package BEDC.FKernel.NameCert BEDC.FKernel.Settled BEDC.GroundCompiler.ChannelEncoding
cd /Users/auric/newmath/lean4 && lake exe rule110-cross-check
cd /Users/auric/newmath && python3 tools/check-axioms.py
```

```bash
# 仓库状态:
git worktree list                        # 只 1 个 (主 worktree)
git branch | grep loop-                  # 空
git log --oneline -1                     # 在 Task 7.6 push 后的 SHA
```

```bash
# CI: pr-gate.yml 全绿.
gh pr checks 109                         # 或当前 PR 号; 全 SUCCESS
```

ROADMAP + STATUS + cross-check 三方一致, Tier A ship 状态明确, Lean kernel 显式不在 trust path (ROADMAP 第一节就写清).

---

## 风险与回滚

**风险 1**: Task 3 解 7 处 conflict 时手滑, 把 L4.4 的 FAIL kind 分类去掉.
- 检测: Task 3.5 build 不过 (函数引用 missing), 或 Task 7.3 cross-check 跑出来缺 FAIL kind 信息.
- 回滚: `git reset --hard <pre-merge-SHA>`, 重新 merge.

**风险 2**: Task 4/5 ROADMAP conflict 手工解错, 误把 worker 的旧 ROADMAP 段塞回 trunk 新 ROADMAP.
- 检测: Task 7.1 build/test 可能仍过, 但 ROADMAP 内容出现矛盾段落.
- 回滚: 类似风险 1; 或者再次 Edit ROADMAP 把误塞内容删掉.

**风险 3**: Task 6 删 L5.2/L5.8 之后用户后悔.
- 缓解: branch reflog 保留 30 天, work 不真丢
- 恢复: `git checkout -b loop-L5-2-realup cc471df00` 或对应 SHA

**风险 4**: push 撞上 codex-auto-dev worker 触发 rebase 风暴.
- 缓解: Task 7.5 检查活跃度选安静窗口
- 回滚: 不需要, codex worker 现在能自己 handle conflict (per CLAUDE.md 历史教训)

**全局回滚**: 任何阶段出问题, 都可以 `git reset --hard 7f17344a8` 回到本 plan 起点 (spec commit 之后但 plan 实施之前).
