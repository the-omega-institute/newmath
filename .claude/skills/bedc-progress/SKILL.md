---
name: bedc-progress
description: 深入分析 BEDC 项目（newmath repo）当前形式化进度、健康度与规模。调用项目自带 Python/Shell 脚本（bedc_ci.py、check-axioms.py、critical_path.py、build_dossier_status.py 等）汇总数据，输出中文进度评估报告。当用户询问"项目进度""形式化到什么程度""项目健康度""规模""ship 状态""下一步该攻什么"或类似主题时触发。
---

# BEDC 进度评估

把已有脚本的输出汇总成一份**中文进度评估报告**。不要 reinvent — 项目脚本已经是真理来源。

## 两档模式

用户没特别说明就跑 **quick**（≤30s）。用户说"完整""ship 评估""走五项"才跑 **full**（含 `lake build` 和 `make`，5–15 min）。

### quick — 元数据 + 静态审计

并行跑这一组，全部从 repo root（`/Users/auric/newmath`）：

```bash
python3 lean4/scripts/bedc_ci.py inventory
python3 lean4/scripts/bedc_ci.py audit
python3 tools/check-axioms.py
python3 lean4/scripts/check_kernel_minimality.py
python3 lean4/scripts/critical_path.py
git log --since="24 hours ago" --pretty=format:"%h" --no-merges | wc -l
git log --since="7 days ago"  --pretty=format:"%h" --no-merges | wc -l
git log --oneline -10 --no-merges
gh run list --branch codex-auto-dev --limit 5 --json status,conclusion,createdAt
gh run list --branch feature/dossier --limit 3 --json status,conclusion,createdAt
ls -la papers/bedc/build/*.pdf docs/dossier/data/*.json 2>/dev/null
```

加跑一组直接的语料统计（grep/find/wc，cheap）：

```bash
find lean4/BEDC -name "*.lean" | wc -l                       # lean 文件数
find lean4/BEDC -name "*.lean" -exec cat {} + | wc -l        # lean LOC
find papers/bedc/parts -name "*.tex" | wc -l                 # tex 文件数
find papers/bedc/parts -name "*.tex" -exec cat {} + | wc -l  # tex LOC
grep -rE "^theorem |^lemma " lean4/BEDC/ | wc -l             # 定理 + lemma
grep -rE "^def |^inductive |^structure |^class " lean4/BEDC/ | wc -l  # def/struct
grep -rh "leanchecked{"  papers/bedc/parts/ | wc -l           # 主实现 marker
grep -rh "leanvariant{"  papers/bedc/parts/ | wc -l           # 变体 marker
grep -rh "leanstmt{"     papers/bedc/parts/ | wc -l           # 仅声明 marker
grep -rh "leandef{"      papers/bedc/parts/ | wc -l           # 定义 marker
```

### full — 加跑 ship 全套

```bash
( cd lean4 && lake build ) 2>&1 | tail -30
( cd papers/bedc && make ) 2>&1 | tail -20
python3 lean4/scripts/bedc_ci.py axiom-purity --strict 2>&1 | tail -20
python3 lean4/scripts/bedc_ci.py manifest-check 2>&1 | tail -20
```

CLAUDE.md 定义的 ship 五项必须全 exit 0：`lake build` / `make` / `check-axioms.py` / `bedc_ci.py audit` / `bedc_ci.py axiom-purity`。

## 报告模板

按下面六块组装中文报告。一定有数字、一定标 ✓/⚠/✗。

```markdown
## BEDC 进度评估（YYYY-MM-DD）

### 1. 规模
- Lean: <N> 文件 / <N> LOC / <N> 定理+lemma / <N> def·struct·class
- 论文: <N> tex 文件 / <N> LOC / <N> 章节标签
- Marker: <N> leanchecked + <N> leanvariant + <N> leanstmt + <N> leandef = <N>

### 2. 硬不变量
- axiom: <0> ✓ / `tools/check-axioms.py` 状态
- sorry: <0> ✓ / 直接 grep 结果
- mathlib-free: ✓ (lakefile.lean 不 require mathlib)
- kernel 最小性: <check_kernel_minimality.py 结果> ✓/✗

### 3. 论文 ↔ Lean 对齐
- `bedc_ci.py audit` 状态（drift / forbidden constructs / case-only-different paths）
- `bedc_ci.py manifest-check` 状态（如跑了 full）

### 4. 当前主攻 domain
- 从 `critical_path.py` 输出取 top —— 这是 codex pipeline 下一轮的目标
- 如果 top=[]，说明 saturation 已到，需要扩展 horizon

### 5. 活跃度
- 24h 非 merge commit: <N>
- 7d  非 merge commit: <N>
- 最近 10 条 commit 主题（看出在哪个 domain 用力）
- codex-auto-dev / feature/dossier 最近 CI 结果

### 6. Dossier & build 产物
- papers/bedc/build/bedc_<UTC>.pdf 是否存在 + mtime
- docs/dossier/data/*.json 是否最新（mtime 比 lean LOC 新）

### 7. 风险与建议
- 任一硬不变量失守 → ✗ 阻断 ship
- audit 报错（drift）→ marker 与 Lean 不一致，要 paper-side 修
- critical_path top=[] → 需要在 horizon 表里加新 domain
- 7d 活跃度低于历史均值 → codex worker 可能僵死
```

## 读输出的要点

- **`bedc_ci.py inventory`** 一行格式：`lean_files=N declarations=N field_targets=N part_labels=N lean_markers=N`
- **`bedc_ci.py audit`** 同样一行，若 exit≠0 输出额外的 violation 列表，全部贴到报告
- **`check-axioms.py`** 末行 `Axiom audit: 0 axioms in lean4/BEDC/. Project invariant holds.` 才算 ✓
- **`critical_path.py`** 输出 JSON，看 `top[].name` 字段；空数组要标记
- **`lake build`** 末尾若有 `Build completed successfully` 即 ✓；任何 error 要把上下文 5 行贴上
- **`make`**（论文）末尾若产出 `bedc.pdf` 即 ✓

## 不要做的事

- 不要为了"完整"而擅自跑 `lake build` —— 它要好几分钟，等用户明确要求 full
- 不要跑 `codex_formalize.py` / `codex_revise.py` —— 那是 worker，不是审计
- 不要写新 Python 脚本 —— 已有的够用，缺什么就在这个 skill 里加 bash 一行
- 不要把"建议"写成行动清单 —— 只标风险，让用户决定下一步
