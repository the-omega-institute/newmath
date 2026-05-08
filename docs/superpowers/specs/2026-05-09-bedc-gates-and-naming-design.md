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

**无例外**: 一律全 paper 唯一. `lean_scaffold_contract.tex` 中的 marker 当前都是 `\leanvariant` 居多, 跟外部唯一冲突的只有 1 处, 一并改 `\leanvariant`. CLAUDE.md §41.4 的 "一站式" 描述与 leanvariant 性质一致 — contract 是摘要不是 first-publish site, 用 leanvariant 自然.

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

完整调查后实际重复:
- **`\leanchecked`: 36 个 X** (有些是同文件内 2 个 occurrence, 有些跨文件)
- **`\leantarget`: 5 个 X**

规则简化为机械式:
- 对每个重复 X, 按 file:line 排序, **首个 occurrence 留原 marker**, 其余全部改 `\leanvariant`
- 无 contract 文件特殊例外 — 即使 `lean_scaffold_contract.tex` 中的 marker 也按规则处理 (它跟外部唯一冲突的只有 1 处)

执行时用一次性 helper python 脚本批量找出 + 改, 跑完人工 git diff 复核, 再 commit.

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
