---
name: bedc-progress
description: 深入分析 BEDC 项目（newmath repo）的理论内容与发展状态，找出潜在问题。调用项目自带脚本（bedc_ci.py、check-axioms.py、check_tex_size.sh、critical_path.py）+ 直接 grep / git log，从五个维度切：理论结构骨架、形式化饱和度地图、开放问题清单、张力点（停滞/反复打磨/违规）、综合判断。当用户询问"项目进度""理论发展""形式化到哪""自指部分到哪""有什么问题""ship 状态""下一步攻什么"或类似主题时触发。
---

# BEDC 理论进度深度分析

不报数字 dashboard——产出**带判断的理论现状报告**。每个数字必须配解读。

## 工作目录

所有命令从 repo root（`/Users/auric/newmath`）跑。

## 五个维度的命令池

### A. 理论结构骨架（必跑）

```bash
python3 lean4/scripts/bedc_ci.py inventory
python3 tools/check-axioms.py
python3 lean4/scripts/check_kernel_minimality.py
echo "FKernel files: $(find lean4/BEDC/FKernel -name '*.lean' | wc -l)"
echo "Derived files: $(find lean4/BEDC/Derived -name '*.lean' | wc -l)"
echo "BaseReflection files: $(find lean4/BEDC/BaseReflection -name '*.lean' | wc -l)"
echo "FKernel inductive: $(grep -rE '^inductive ' lean4/BEDC/FKernel/ | wc -l)"
echo "Total inductive: $(grep -rE '^inductive ' lean4/BEDC/ | wc -l)"
echo "Total structure: $(grep -rE '^structure ' lean4/BEDC/ | wc -l)"
echo "Total class: $(grep -rE '^class ' lean4/BEDC/ | wc -l)"
for s in AskSetup PackageSetup DomainSetup NameCertSetup BaseReflectionSetup; do
  echo "$s instances: $(grep -rE "$s" lean4/BEDC/ | grep -i instance | wc -l)"
done
```

### B. 形式化饱和度地图（必跑）

每个顶层目录的 leanchecked 密度。这是判断"哪一片理论已闭环、哪一片仍开放"的一手数据。

```bash
for d in papers/bedc/parts/*/; do
  labels=$(grep -rh "\\\\label{" "$d" 2>/dev/null | wc -l)
  checked=$(grep -rh "leanchecked{" "$d" 2>/dev/null | wc -l)
  files=$(find "$d" -name '*.tex' | wc -l)
  if [ "$labels" -gt 0 ]; then
    pct=$(awk "BEGIN{printf \"%.1f\", $checked*100/$labels}")
  else pct="—"; fi
  printf "%-40s files=%3d labels=%4d checked=%4d  %s%%\n" "${d#papers/bedc/parts/}" "$files" "$labels" "$checked" "$pct"
done | sort -k4 -t= -rn
```

### C. 开放问题清单（必跑）

仅有声明、未证完的目标 + 论文里"ProofTarget"标记 + proof_obligations 章节明细。这是 BEDC 的**真正开口**。

```bash
echo "=== leanstmt（仅声明，无证明）==="
grep -rh "leanstmt{" papers/bedc/parts/ 2>/dev/null | sort -u
echo ""
echo "=== ProofTarget mentions ==="
grep -rc "ProofTarget" papers/bedc/parts/ 2>/dev/null | grep -v ":0$"
echo ""
echo "=== proof_obligations 章节饱和度 ==="
for f in papers/bedc/parts/proof_obligations/*.tex; do
  labels=$(grep -c "\\\\label{" "$f")
  checked=$(grep -c "leanchecked{" "$f")
  pct=$([ "$labels" -gt 0 ] && awk "BEGIN{printf \"%.0f\", $checked*100/$labels}" || echo "—")
  printf "%-50s %3d/%-3d  %s%%\n" "${f##*/}" "$checked" "$labels" "$pct"
done
echo ""
echo "=== capstones 章节文件大小（叙述性高地）==="
wc -l papers/bedc/parts/capstones/*.tex 2>/dev/null | sort -rn | head -10
```

### D. 张力点（必跑）

"哪里反复打磨说明没收敛"+"违反 marker 纪律"+"超 800 行的 tex"+"critical_path 是否仍有可攻 horizon"。

```bash
echo "=== 7d hottest tex（反复打磨域）==="
git log --since="7 days ago" --pretty=format: --name-only --no-merges 2>/dev/null \
  | grep "\\.tex$" | sort | uniq -c | sort -rn | head -10
echo ""
echo "=== 7d hottest lean ==="
git log --since="7 days ago" --pretty=format: --name-only --no-merges 2>/dev/null \
  | grep "lean4/.*\\.lean$" | sort | uniq -c | sort -rn | head -10
echo ""
echo "=== leanchecked marker 纪律违规（同名 ≥2 次）==="
grep -rh "leanchecked{" papers/bedc/parts/ 2>/dev/null \
  | sort | uniq -c | awk '$1>1{print}'
echo ""
echo "=== 800 行红线 ==="
bash papers/bedc/scripts/check_tex_size.sh 2>&1 | grep -E "OVERSIZED|exceeds"
echo ""
echo "=== critical_path 下一目标 ==="
python3 lean4/scripts/critical_path.py 2>&1 | grep -E "top|saturation|threshold"
echo ""
echo "=== 24h / 7d commit 数 ==="
echo "24h: $(git log --since='24 hours ago' --pretty=format:%h --no-merges | wc -l)"
echo "7d:  $(git log --since='7 days ago'  --pretty=format:%h --no-merges | wc -l)"
```

### E. paper↔Lean 漂移（必跑）

```bash
python3 lean4/scripts/bedc_ci.py audit 2>&1 | tail -20
```

audit 任意非 0 退出 / 输出 violation 列表 → 立即贴报告。

### F. 全档（仅在用户要求"完整"或"ship 评估"时）

```bash
( cd lean4 && lake build ) 2>&1 | tail -30
( cd papers/bedc && make ) 2>&1 | tail -20
python3 lean4/scripts/bedc_ci.py axiom-purity --strict 2>&1 | tail -20
python3 lean4/scripts/bedc_ci.py manifest-check 2>&1 | tail -20
```

## 报告框架（中文，五块带判断）

```markdown
## BEDC 理论进度深度分析（YYYY-MM-DD）

### 1. 理论结构骨架
- FKernel <N> 文件 / Derived <N> / BaseReflection <N>
- inductive <N> 个（FKernel <N> + Derived <N>）/ structure <N> / class <N>
- 4 类 setup 实例：AskSetup <N> / PackageSetup <N> / DomainSetup <N> / NameCertSetup <N>
- 硬不变量：0 axiom ✓ / 0 sorry ✓ / kernel 隔离 ✓
- **判断**：<一句话——FKernel 体量 vs Derived 体量比说明什么；某 setup class 实例数为 0 是不是异常>

### 2. 形式化饱和度地图
按密度从高到低列每个顶层目录，标 ✓ / ⚠ / 文本性章节 (—)：
- core <pct>% — 核心 <已闭环 / 仍在动>
- concrete_instances <pct>% — 主战场 <在 X 域用力>
- capstones <pct>% — <叙述章节，正常 / 异常空白>
- acceptance <pct>% — <规范性章节，本就不形式化 / 应有但缺>
- ...
- **判断**：<哪一片已饱和（>85% + 7d 无修改 = 稳定）；哪一片仍在主推（中密度 + 高 churn）；哪一片是结构性空白>

### 3. 开放问题清单
- leanstmt（仅声明）共 <N> 条，按命名空间归类：
  - `BEDC.Reflection.*` <N> 条（自指闭环：<列出涉及的命题，如 two_loops_theorem / halting_as_form_of_distinction_fixed_point / compilation_as_namecert_morphism>）
  - `BEDC.FKernel.Ask/Package.*Policy` <N> 条
  - 其他 <N> 条
- ProofTarget 论文标记：<N> 个章节 / 共 <N> 处
- proof_obligations/ 各章饱和度：<列名最低的 2-3 个>
- **判断**：<最大开口在哪？是 Reflection 自指部分？还是某 obligation 章节？>

### 4. 张力点
- **反复打磨域**（7d hottest tex top 3）：<列名 + 改动次数>。说明 <Field 收尾困难 / Option 在重写 / 等>
- **stale 文件**（capstones 等纯文本章节最近 30d 无 churn）：<是否有>
- **marker 纪律违规**：<N> 条 leanchecked 同名出现 ≥2 次 — 应改为 leanvariant 或合并
- **800 行红线**：<列出超长文件 + 行数>
- **critical_path top**：<[] = 已饱和 / [{name=...}] = 下一攻击域>
- **活跃度**：24h <N> / 7d <N>，<极高 / 正常 / 偏低>

### 5. 综合判断 + 潜在问题
列 3-5 条具体可操作判断，每条带证据：
1. **<一句话结论>** — 证据：<具体数字 / 文件 / 标签>。风险：<如不处理会怎样>
2. ...

最末标 ship 五项快档状态：audit ✓ / check-axioms ✓ / kernel-minimality ✓ / lake build (full) / make (full)。
```

## 解读规则（数据点 → 判断）

- **某顶层目录 leanchecked 密度 < 30% 且非 governance/acceptance** → 结构性空白，标 ⚠
- **leanstmt 集中在 BEDC.Reflection.\*** → 自指闭环未收尾，BEDC 元层最大开口
- **critical_path top=[]** → horizon 已饱和；如 7d commit 仍高，pipeline 在精修而非扩展，需考虑加新 domain
- **某 tex 文件 7d 修改 ≥ 100 次** → 反复打磨，要不就是难收敛要不就是 codex worker 在该域抢工
- **leanchecked 同名出现 ≥2 次** → CLAUDE.md "每个 Lean 目标只标 1 次" 违规，第二次以后应改 leanvariant
- **超 800 行的 tex** → CLAUDE.md 红线，阻塞 PDF build（即便 check_tex_size.sh exit 0 是 advisory）
- **paper labels 比 lean markers 多 ≥1000** → 大量论文叙述未形式化引用；要看是否本应如此（capstones / acceptance 类）
- **某 inductive 在 FKernel 但其 derived predicate 仅有 def 没 theorem** → 闭生成类型悬空，常见于新加但没补完 lemma 的情况

## 不要做的事

- 不要为了"完整"而擅自跑 `lake build` —— 它要好几分钟，等用户明确要求 full
- 不要跑 `codex_formalize.py` / `codex_revise.py` —— 那是 worker，不是审计
- 不要写新 Python 脚本 —— 已有的 + bash 一行够用
- 不要堆数字而不下判断 —— 每节"判断"必须给出对理论现状的具体读法
- 不要重复 CLAUDE.md 已写明的不变量当成"成就"（0 axiom 0 sorry mathlib-free 是 baseline，不是进度）
