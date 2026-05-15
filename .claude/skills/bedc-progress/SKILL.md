---
name: bedc-progress
description: 深入分析 BEDC 项目（newmath repo）的理论内容与发展状态，找出潜在问题与漂移点。从五个维度切入：理论结构骨架、形式化饱和度地图、开放问题清单、张力点、综合判断。当用户询问"项目进度""理论发展""形式化到哪""自指部分到哪""有什么问题""ship 状态""下一步攻什么"或类似主题时触发。
---

# BEDC 理论进度深度分析

不报数字 dashboard——产出**带判断的理论现状报告**。每个数字必须配解读。

## 信息治理纪律 (必读)

本 skill **不复述当前事实**——具体数字、命名空间命中点、热点目录、阈值都会过时。本 skill 只承载:

- **查询方法**: 用什么命令读取哪些数据源
- **解读框架**: 数据出来后怎么组合成判断
- **漂移检测**: 实际跟 CLAUDE.md 不符时怎么报告

**唯一真实源**:
- 项目规范 → `/Users/auric/newmath/CLAUDE.md`
- 工具能力 → 各脚本的 `--help`
- 形式化事实 → `lean4/BEDC/` + `papers/bedc/parts/` 实际内容
- 实时数据 → `bedc_ci.py` / `critical_path.py` / `grep` 输出

**冲突处理**: skill 给出的方法跟实际工具输出不一致 (脚本子命令变了 / 等级名变了 / 输出格式变了) → 信工具, 在报告里列"漂移点", 不要默默套用旧方法。

## 工作目录

所有命令从 repo root（`/Users/auric/newmath`）跑。

## 维度 A: 理论结构骨架

读 Lean 端体量与硬不变量。先用工具 `--help` 看当前可用子命令, 再选合适的跑:

```bash
python3 lean4/scripts/bedc_ci.py --help
python3 lean4/scripts/bedc_ci.py inventory                     # 总量摘要
python3 tools/check-axioms.py                                  # 0 axiom 不变量
python3 lean4/scripts/check_kernel_minimality.py               # kernel 隔离
```

骨架计数 (随用随取):

```bash
find lean4/BEDC/FKernel -name '*.lean' | wc -l
find lean4/BEDC/Derived -name '*.lean' | wc -l
find lean4/BEDC/BaseReflection -name '*.lean' | wc -l
grep -rE '^inductive ' lean4/BEDC/ | wc -l
grep -rE '^structure ' lean4/BEDC/ | wc -l
grep -rE '^class ' lean4/BEDC/ | wc -l
```

**解读问** (不预设答案, 拿到数字自己判断):
- FKernel 体量 vs Derived 体量比说明什么? (核心保持紧, 还是膨胀了?)
- inductive / structure / class 总量是不是合理? (有没有意外暴增?)
- 0 axiom / 0 sorry / kernel-minimality 是否仍守住? (这是 baseline, 不是进度)

## 维度 B: 形式化饱和度地图

两个粒度: label 级 (细粒度) 与章节级 (粗粒度)。**都报, 不互相替代**。

**Label 级 (leanchecked / labels):**

```bash
for d in papers/bedc/parts/*/; do
  labels=$(grep -rh "\\\\label{" "$d" 2>/dev/null | wc -l)
  checked=$(grep -rh "leanchecked{" "$d" 2>/dev/null | wc -l)
  files=$(find "$d" -name '*.tex' | wc -l)
  if [ "$labels" -gt 0 ]; then
    pct=$(awk "BEGIN{printf \"%.1f\", $checked*100/$labels}")
  else pct="—"; fi
  printf "%-40s files=%4d labels=%5d checked=%5d  %s%%\n" "${d#papers/bedc/parts/}" "$files" "$labels" "$checked" "$pct"
done | sort -k4 -t= -rn
```

**章节级 (formalstatus 等级分布):**

```bash
grep -rh "\\\\formalstatus{" papers/bedc/parts/ 2>/dev/null \
  | grep -oE "\\\\[a-zA-Z]+V" | sort | uniq -c | sort -rn
grep -rh "\\\\theoryclosure{" papers/bedc/parts/ 2>/dev/null \
  | grep -oE "\\\\[a-zA-Z]+Closure" | sort | uniq -c | sort -rn
```

**解读问**:
- 哪一片目录已饱和? (高密度 + 7d 改动稀疏 → 稳定)
- 哪一片是主战场? (中密度 + 7d 高 churn)
- 哪一片是结构性空白? (低密度且非 governance / acceptance / visions 这类规范+叙述章)
- 章节级 unformalizedV 比例跟 label 级 saturation 之间差多少? (前者高出很多 → 有大量章节连"目标"都没标)

CLAUDE.md 给出 closurestatus 等级名集 (`seedClosure | obligationClosure | scopedClosure | publicClosure | bridgedClosure | matureClosure`); 若 grep 出来的等级名跟 CLAUDE.md 不符, **列为漂移**。

## 维度 C: 开放问题清单

仅声明未证 + 漂移章节 + 章节级未形式化:

```bash
echo "=== leanstmt（仅声明，无证明）==="
grep -rh "leanstmt{" papers/bedc/parts/ 2>/dev/null | sort -u

echo ""
echo "=== 章节级 unformalizedV ==="
grep -rl "\\\\formalstatus{\\\\unformalizedV}" papers/bedc/parts/ 2>/dev/null \
  | awk -F/ '{print $4}' | sort | uniq -c | sort -rn

echo ""
echo "=== bedc_ci.py 当前 audit 子命令清单 ==="
python3 lean4/scripts/bedc_ci.py --help

echo ""
echo "=== marker existence audit (X 必须在 lean4/BEDC/ 真存在) ==="
python3 lean4/scripts/bedc_ci.py marker-existence-audit 2>&1 | tail -20

echo ""
echo "=== critical_path drift_chapters (理论闭合 vs 形式化等级不一致) ==="
python3 lean4/scripts/critical_path.py 2>/dev/null \
  | python3 -c "import json,sys; d=json.load(sys.stdin); print(f'drift_chapters_total: {d.get(\"drift_chapters_total\", \"N/A\")}'); print(f'open_horizons: {d.get(\"open_horizons\", \"N/A\")}'); print(); [print(f'  {c[\"name\"]:30s} theory={c[\"theory_grade\"]:18s} formal={c[\"formal_grade_token\"]:18s} → 目标 {c[\"objective_formal_grade\"]:15s} thms={c[\"thms\"]}') for c in d.get('drift_chapters', [])]"
```

**解读问**:
- leanstmt 集中在哪个命名空间? (按 prefix 分组; 集中在某子系统 → 那是开口; 散落 → 没系统性开口)
- 章节级 unformalizedV 集中在哪个顶层目录? (若集中在 concrete_instances 类长尾, 是产线节奏问题; 若集中在 core / proof_obligations, 是结构性问题)
- marker-existence-audit 是否有 missing? (有 missing → drift, 必须修)
- critical_path drift_chapters 是哪些? (这是"自我宣称 vs 实际形式化"不一致的真漂移, 应该解读最大的几个)

## 维度 D: 张力点

反复打磨 / 纪律违规 / 红线 / 活跃度 / horizon:

```bash
echo "=== 7d hottest tex ==="
git log --since="7 days ago" --pretty=format: --name-only --no-merges 2>/dev/null \
  | grep "\\.tex$" | sort | uniq -c | sort -rn | head -15

echo ""
echo "=== 7d hottest lean ==="
git log --since="7 days ago" --pretty=format: --name-only --no-merges 2>/dev/null \
  | grep "lean4/.*\\.lean$" | sort | uniq -c | sort -rn | head -15

echo ""
echo "=== leanchecked marker 纪律违规 (同名 ≥2 次, CLAUDE.md '只标 1 次' 规范) ==="
grep -rh "leanchecked{" papers/bedc/parts/ 2>/dev/null \
  | sort | uniq -c | awk '$1>1{print}'

echo ""
echo "=== 800 行红线 ==="
bash papers/bedc/scripts/check_tex_size.sh 2>&1 | grep -E "OVERSIZED|exceeds"

echo ""
echo "=== critical_path horizon 摘要 ==="
python3 lean4/scripts/critical_path.py 2>/dev/null \
  | python3 -c "import json,sys; d=json.load(sys.stdin); print('closed_horizons:', d.get('closed_horizons', {})); print('open_horizons:', d.get('open_horizons')); print('formal_axis_top_total:', d.get('formal_axis_top_total')); top=d.get('top',[])[:5]; [print(f'  top[{i}]: {t.get(\"name\",\"?\")} deps={t.get(\"deps\",[])[:3]}') for i,t in enumerate(top)]"

echo ""
echo "=== 活跃度 ==="
echo "24h: $(git log --since='24 hours ago' --pretty=format:%h --no-merges | wc -l) commits"
echo "7d:  $(git log --since='7 days ago'  --pretty=format:%h --no-merges | wc -l) commits"
echo ""
echo "(过滤 registry / preamble / main.tex 噪音再看真正改动:)"
git log --since="7 days ago" --pretty=format: --name-only --no-merges 2>/dev/null \
  | grep -E "\\.(tex|lean)$" \
  | grep -vE "preamble\\.tex|main\\.tex|BEDC\\.lean$|_index" \
  | sort | uniq -c | sort -rn | head -10
```

**解读问** (拿到当前数字自己判断, 不预设阈值):
- hottest 文件除了 registry / 索引性文件 (preamble.tex / main.tex / BEDC.lean), 哪些**内容性**文件高 churn? 这些是当前主推前线还是难收敛?
- horizon: `closed_horizons` 各等级分布如何? `open_horizons` 数量? top 几个 horizon 名字暗示当前 codex 准备攻什么?
- marker 违规与 800 行红线是硬 invariant, 任何非零都该立即报告
- 活跃度看绝对值意义不大 (codex worker 节奏决定数量级), 看**比例**: 多少进 main? 多少滞留 auto-dev? `git rev-list --count origin/main..origin/auto-dev` 给治理性张力数字

## 维度 E: paper ↔ Lean 漂移

```bash
python3 lean4/scripts/bedc_ci.py audit 2>&1
python3 lean4/scripts/bedc_ci.py marker-existence-audit 2>&1 | tail -10
```

`audit` 任意非 0 退出 → 立即贴报告。`marker-existence-audit` 若 missing > 0 → 立即贴报告。

Lean declarations 与 paper markers 的 gap 也值得看 (Lean 端独立增长 vs paper 端未引用):

```bash
inv=$(python3 lean4/scripts/bedc_ci.py inventory 2>/dev/null)
echo "$inv"  # 含 declarations / lean_markers / part_labels
```

`declarations - lean_markers` 即 "Lean 端有但 paper 没引"; 这个差里 carrier / helper def 是正常的, 但比例过大值得抽查。

## 维度 F: 全档 (仅在用户明确要 "完整" / "ship 评估" 时跑)

```bash
( cd lean4 && lake build ) 2>&1 | tail -30
( cd papers/bedc && make ) 2>&1 | tail -20
python3 lean4/scripts/bedc_ci.py axiom-purity --strict 2>&1 | tail -20
python3 lean4/scripts/bedc_ci.py metacic-purity 2>&1 | tail -20
python3 lean4/scripts/bedc_ci.py manifest-check 2>&1 | tail -20
```

## 报告框架 (五块带判断)

```markdown
## BEDC 理论进度深度分析 (YYYY-MM-DD)

### 0. 漂移点 (若有)
- 实际工具输出跟 CLAUDE.md / 文档不一致的地方
- 例: 等级名不符 / 子命令清单变化 / 输出格式变化
- 漂移点必须在最前, 否则后面判断可能建在错前提上

### 1. 理论结构骨架
- FKernel / Derived / BaseReflection 文件数, inductive / structure / class 总量, setup 实例数
- 硬不变量 (0 axiom / 0 sorry / kernel-minimality / audit / marker-existence) 状态
- **判断**: 核心是否仍紧, 长尾是否暴增, 哪里值得抽查

### 2. 形式化饱和度地图
- 按密度从高到低列每个顶层目录 (label 级)
- 章节级 formalstatus 分布 (unformalizedV / theoremCheckedV / auditCleanV / ...)
- **判断**: 哪一片已饱和, 哪一片主战场, 哪一片结构性空白

### 3. 开放问题清单
- leanstmt 总数与命名空间分布
- 章节级 unformalizedV 在哪个顶层目录最集中
- critical_path drift_chapters 详情 (前 5 最大 thms 数量的)
- proof_obligations 章节饱和度
- **判断**: 最大开口在哪, 是元层 (kernel / MetaCIC) 还是某 obligation 章节

### 4. 张力点
- 反复打磨 (过滤 registry 后的 hottest 内容性文件)
- marker 纪律违规与 800 行红线 (任何非零都要报)
- critical_path top horizon (下一可攻域)
- 治理张力 (main vs auto-dev 距离)
- **判断**: codex 在攻什么, 在停在什么, 哪里需要人工介入

### 5. 综合判断 + 潜在问题
3-5 条具体可操作判断, 每条带证据 + 风险

最末标 ship 五项: audit / check-axioms / kernel-minimality / lake build / make
```

## 写报告时的纪律

- **不预设阈值**: skill 不写 "≥ 100 次 = 反复打磨" 这种阈值, 让模型看到具体数字自己判断"这个数字在当前 codex 节奏下是高还是正常"
- **不预设命名空间命中点**: 不写 "leanstmt 集中在 BEDC.Reflection.\*", 让模型 grep 当前 leanstmt 自己分组判断
- **保留对 CLAUDE.md 不变量的引用**: 0 axiom / 0 sorry / mathlib-free / 等级名集 / 800 行红线 — 这些是规范, CLAUDE.md 是源, skill 引用但不复述
- **不要堆数字**: 每块"判断"段必须给出对当前数据的具体读法; 看到 "这是 baseline" 的事实不当 "进度"
- **漂移优先**: 若发现 skill 命令 / CLAUDE.md 规范 / 工具输出格式之间不一致, 在报告"漂移点"段先列出, 让用户判断

## 不要做的事

- 不要为了"完整"擅自跑 `lake build` — 几分钟, 等用户明确要求
- 不要跑 `codex_formalize.py` / `codex_revise.py` — 那是 worker, 不是审计
- 不要为了"显得严谨"重复 CLAUDE.md 的不变量当成"成就"
- 不要复述项目结构 / 子命令清单 / 文件路径列表 — 这些已经在 CLAUDE.md / `--help` / `find` 里, 重复就是漂移源
