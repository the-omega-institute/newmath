# BEDC PDF make 门禁升级 + 文件命名规范化

设计文件 — 一次性把 `papers/bedc/` 的 build-time 门禁补齐, 并把不合命名规范的现存文件搬到位.

## 目标

1. **门禁** 从 "事后被 worker fix" 升级到 "build 前直接 fail-fast", 让作者本地立刻看到违规, 不再依赖 silent rewrite 或 worker 兜底.
2. **命名规范** 在 `parts/concrete_instances/` 一级建立单一形式 `^[0-9]+[a-z]?_<concept>_…\.tex$`; subdir 内不强制.
3. **现存违规** 一次性改干净, 留下 0 违规 baseline, 之后门禁就是单调 invariant.

## 工作流

- 当前在 `auto-dev`, 先 `git pull --ff-only` 同步远端 25 commits.
- 切新分支 `gates-and-naming`, 全程在该分支.
- **原子单 commit** (CLAUDE.md 协作纪律): 脚本 + rename + split + marker fix 全打成一个 commit, 推送前每一步 `make check` 通过.
- 验证通过后 push, 在 GitHub 开 PR 回 `auto-dev`.

## 1. 门禁脚本

接进 `papers/bedc/Makefile precheck`:

```make
precheck:
	@bash scripts/check_tex_size.sh
	@bash scripts/check_math_env.sh
	@python3 scripts/check_marker_uniqueness.py
	@python3 scripts/check_naming.py
```

### 1.1 `scripts/check_tex_size.sh` (改一行)

`-gt` → `-ge`. ≥800 行即 fail. 修复 5 个触顶文件后这条就立即生效.

### 1.2 `scripts/check_math_env.sh` (改行为)

从 silent rewrite 改 fail-fast. 检测到 `\begin{equation|equation*|align|align*|eqnarray|eqnarray*}` 或顶层 `\[...\]`, 就打印 file:line 列表, exit 1. 不再隐式重写.

理由: silent rewrite 让作者看不到自己写错了, 也让 git diff 出现门禁制造的二次改动. fail-fast 一行报错即可指导作者改.

### 1.3 `scripts/check_marker_uniqueness.py` (新)

扫 `papers/bedc/parts/**/*.tex` 与 `papers/bedc/frontmatter/**/*.tex`, `papers/bedc/appendices/**/*.tex` (**只扫 .tex, 不扫 .md** — `HOW_INCREMENT_WORKS.md` 中的 `\leanchecked{X}` 是教学示例占位符, 不属于 marker), 提取所有 `\leanchecked{X}` 和 `\leantarget{X}`. 同 X 出现 ≥2 次 fail, 输出 `X` 的 file:line 列表.

**例外**: `parts/proof_obligations/lean_scaffold_contract.tex` 是 CLAUDE.md §41.4 显式认可的"一站式"摘要块, 这个文件中的 marker 不计入唯一性检查 (但会计入"已经在别处出现过"的判断 — 即不允许其他文件指向它已经记录的 X 之外, 它本身可以多次列举).

实现细节: 把 `lean_scaffold_contract.tex` 中的 X 收集进 contract-only 集合; 主扫描发现某 X 在非 contract 文件中出现 ≥2 次即 fail. contract-only 中重复出现不报错.

### 1.4 `scripts/check_naming.py` (新)

扫 `papers/bedc/parts/concrete_instances/` **一级** .tex 文件 (不含 subdir 内). 文件名必须匹配:

```
^[0-9]+[a-z]?_[a-z][a-z0-9_]*\.tex$
```

例: `04_nat_namecert_construction.tex` ✓, `35b_compact_image_total_bounded.tex` ✓, `hilbert_orthogonal_projection_row.tex` ✗.

**只管 `concrete_instances/` 一级**. 其他主题目录 (`core/`, `capstones/`, `ground_compiler/`, `proof_sprint/`, `proof_obligations/`, ...) 一概不检查 — 各主题已经各自有内部约定 (capstones 用语义命名, proof_sprint 用 `NN_*`, 等等), 不强行统一. concrete_instances 一级是当前唯一有 broken outliers 的位置, 也是规模最大 (250+ 文件), 加 gate 收益最高.

`concrete_instances/` 内的 subdir (如 `hilbert/`) 也不检查 — subdir 是 split 出来的实现细节, 命名跟主题就好.

## 2. 命名违规修复

`papers/bedc/parts/concrete_instances/` 一级有 10 个不合规的 flat 文件 (`35b_*` 已合规, 不动). 处理:

| 现路径 | 处置 |
|---|---|
| `hilbert_orthogonal_projection_row.tex` | → `hilbert/orthogonal_projection_row.tex` |
| `hilbert_orthogonal_residual_decomposition.tex` | → `hilbert/orthogonal_residual_decomposition.tex` |
| `cyclotomic_downstream_namecert_obligation_packet.tex` | → `cyclotomic/downstream_namecert_obligation_packet.tex` |
| `galoisgroup_group_law_package.tex` | → `galoisgroup/group_law_package.tex` |
| `numfield_rat_reflexive_namecert_obligations.tex` | → `numfield/rat_reflexive_namecert_obligations.tex` |
| `numfield_reflexive_public_interfaces.tex` | → `numfield/reflexive_public_interfaces.tex` |
| `quotientgroup_abelian_terminal_projection.tex` | → `quotientgroup/abelian_terminal_projection.tex` |
| `compactmetric_public_interface.tex` | 新建 `compactmetric/`, → `compactmetric/public_interface.tex` |
| `numfield_rat_reflexive_obligations.tex` (1 行死 wrapper, 没 \input 引用) | **删除** |

`mv` 后, 找到引用方 `\input{parts/concrete_instances/<旧名>}` 全部改成新路径. grep 已确认引用方:
- `parts/concrete_instances/69_hilbert_namecert_construction.tex`
- `parts/concrete_instances/107_compactmetric_namecert_construction.tex`
- `parts/concrete_instances/cyclotomic/certificate.tex`
- `parts/concrete_instances/quotientgroup/concrete_namecert_certificate.tex`
- `parts/concrete_instances/numfield/reflexive_namecert.tex`
- `parts/concrete_instances/numfield_rat_reflexive_obligations.tex` (即将删除, 不更新)

## 3. 触顶文件 split

5 个文件 ≥ 798 行, cap 严格化后必爆, 必须先 split. 每个按内部 section / 主题边界切, 父文件留 `\input{...}`, **不靠合并空行/压缩空白腾空间** (CLAUDE.md 明文禁止).

| 文件 | 行 | split 策略 |
|---|---|---|
| `parts/core/03_relational_extension_and_continuation.tex` | 800 | 按 ext / cont 两轴切, 形如 `core/relational_ext.tex` + `core/relational_cont.tex`, 父文件留索引 |
| `parts/concrete_instances/list/11_spine_bridge_transport_certificate.tex` | 800 | 按 transport 阶段 / certificate 阶段切 |
| `parts/concrete_instances/list/11_singleton_source_certificate.tex` | 800 | 按 source / certificate 切 |
| `parts/concrete_instances/linearmap/module_linearmap_certificates.tex` | 799 | 按模块 / linearmap 子主题切 |
| `parts/concrete_instances/38_nattrans_namecert_carrier.tex` | 798 | 按 carrier 内的子主题切 |

具体边界在执行时按文件内容确定, 标准是 split 后所有文件都明显低于 800 cap (目标 ≤ 700) 且每个文件主题独立.

## 4. `\leanchecked` / `\leantarget` 唯一性修复

11 个 X 在多 site 出现. 规则:

- 选 canonical primary site: 优先该定理首次发表的 chapter / construction 文件
- `lean_scaffold_contract.tex` 中的引用永远视为变体, 改 `\leanvariant`
- 其余非 canonical site 改 `\leanvariant`

具体每个 X 的 canonical 选择在执行时按 `grep -n "\\leanchecked{X}" parts/` 输出和 site 语义判断, 写在执行计划的 todo 项中.

清单 (从调查得到):

**leanchecked (9 X)**:
- `BEDC.FKernel.Unary.add_up_licensed_not_primitive` (3 site)
- `BEDC.FKernel.Unary.nat_up_interface_seed`
- `BEDC.FKernel.Cont.cont_deterministic`
- `BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_empty_fiber_iff`
- `BEDC.Derived.SheafUp.SheafBHistPointGermLedger_cover_descent_exhaustion`
- `BEDC.Derived.RatUp.rat_history_semantic_name_certificate`
- `BEDC.Derived.RatUp.RatHistoryLedgerPolicy_cont_unary_context_positive_denominators`
- `BEDC.Derived.OptionUp.TaggedOptionHistoryClassifier_endpoint_semantic_fields`
- `BEDC.Derived.NumFieldUp.NumFieldRatReflexive_ledger_exactness`

**leantarget (5 X)**:
- `BEDC.Derived.TensorProductUp.TensorProductSingletonFactor_tensor_semanticNameCert`
- `BEDC.Derived.QuotientGroupUp.QuotientGroupCentralizerNormalizer_semanticNameCert`
- `BEDC.Derived.MetricUp.MetricDistanceWitness_semanticNameCert`
- `BEDC.Derived.GroupUp.GroupSingletonHistory_laws`
- `BEDC.Derived.AbGroupUp.singleton_empty_history_abgroup_laws`

## 5. 验证

push 前必须全过:

```bash
cd papers/bedc && make            # 双趟 PDF, 解析 \autoref / TOC
cd lean4 && lake build            # 0 axiom 0 sorry
python3 tools/check-axioms.py
python3 lean4/scripts/bedc_ci.py audit
python3 lean4/scripts/bedc_ci.py axiom-purity
```

PR 描述里贴 5 条命令的 exit code = 0.

## 不在范围内

- subdir 内文件命名重整 (用户明确不做)
- "hub 文件不含正文环境" 门禁 (调查显示判定边界模糊, 暂不上线)
- 增量叙事禁词 / 数学环境违规 / underscore 等已 0 违规, 不动

## 风险

- **rename 撞 worker**: 用户确认切新分支隔离, worker 在 `codex-auto-dev` 跑, 互不干扰. PR 合并时按 CLAUDE.md "merge 不 rebase".
- **fail-fast math env**: 如果远端有未 push 的违规等待 silent rewrite, 切到 fail-fast 后会立刻 fail. 调查已确认本地 0 违规.
- **marker 改 leanvariant**: 改完要 `bedc_ci.py audit` 跑通 — variant 也是 X 必须真存在的.
