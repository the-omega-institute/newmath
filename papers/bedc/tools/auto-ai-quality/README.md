# AI 产物质量管线

## 目标

本管线用于评审 AI 产生的 BEDC 内容，并把较弱的证书表面压向真正承重的理论目标。它不是新发现管线，也不以增加章节数量为目标。它只回答一个问题：

```text
这份 AI 产物是否真的携带理论压力？
```

如果答案是否定的，管线给出明确的深化目标，让现有 paper 管线或 Lean 管线去执行。

高质量内容至少满足以下一项：

- 阻止一个非法 consumer route；
- 证明 nonescape 或 noninternalization；
- 消解一个已命名 obstruction 的一部分；
- 去掉或缩窄某个条件定理的输入；
- 产生被 endpoint theorem 消费的定理；
- 给出具体 counter-witness 或边界情形；
- 推动 critical path endpoint 更接近闭合。

Carrier row、field projection、tuple unpacking、NameCert package、closure prose 都可以是有用基础设施，但它们本身不算质量进展。

## 适用范围

第一阶段只审查 AI-heavy 内容：

- `papers/bedc/parts/concrete_instances/`；
- `lean4/BEDC/Derived/`；
- `papers/bedc/parts/visions/` 作为只读背景；
- `papers/bedc/parts/conjectures/` 作为只读 open-problem 背景。

优先试点两个区域：

- MetaCIC：subject reduction、substitution compatibility、confluence、normalization、closed consistency；
- Apophatic：noninternalization、no-bypass route、boundary ledger、downstream consumer exactness。

## 非目标

本管线不做以下事情：

- 不以创建新章节为主要输出；
- 不优化读者阅读体验；
- 不添加只有 marker、没有 Lean 内容的改动；
- 不重写 vision 章节，除非走已有的 `\concretizedIn` 纪律；
- 不把 theorem 数量、文件数量、closure token 数量直接当成质量；
- 不放松 mathlib-free、0 axiom、0 sorry 不变量。

## 现有系统中的位置

现有生产链路是：

```text
bedc-deep discovery
  -> paper theorem site
  -> Lean formalization
  -> paper-Lean audit and closure sync
```

质量管线位于生产之后：

```text
AI 产生的 paper / Lean 内容
  -> 质量扫描
  -> review packet
  -> deepening target
  -> 交给现有 paper / Lean 管线
  -> 验证门
```

第一版尽量只生成 review packet 和 deepening target，不直接修改论文或 Lean。直接修改只用于很小的确定性维护任务。

## 候选来源

### AI-origin 章节

扫描包含以下标记的章节：

```text
\origin{ai}
\origin{ai-composite}
```

这是主审查面。AI-origin 章节必须证明自己不是单纯命名 tuple。

### 弱闭合表面

优先选择仍处在以下状态的章节：

```text
seedClosure
obligationClosure
```

如果章节有很多 NameCert / projection 定理，但没有 semantic boundary theorem，优先级提高。

### 低依赖压力章节

优先选择依赖图里入度或出度很低的 AI-origin 章节，尤其是没有下游 theorem 消费的章节。

### Projection-heavy Lean namespace

扫描 Lean namespace 中是否大多是以下形状：

- carrier projection；
- field equality；
- route tuple unpacking；
- direct NameCert packaging；
- assumption echo。

再检查是否缺少以下内容：

- obstruction theorem；
- nonescape theorem；
- exactness theorem；
- endpoint bridge theorem；
- counterexample theorem。

### Critical path 邻近内容

靠近这些 endpoint 的内容优先：

- `BEDC.MetaCIC.subject_reduction`；
- MetaCIC confluence bridge；
- MetaCIC closed-normal consistency assembly；
- Apophatic far-end noninternalization；
- Apophatic consumer no-bypass；
- real-completeness limit seal；
- digest/fiber source-equality refusal。

靠近 endpoint 的内容比孤立 certificate package 更重要。

## Review Packet 结构

每个 review packet 同时有 JSON 和 Markdown 摘要。

JSON 必填字段：

```json
{
  "id": "semantic-slug",
  "chapter_slug": "metacicnormalizationfrontier",
  "origin": "ai",
  "paper_files": [],
  "lean_files": [],
  "primary_namespace": "BEDC.Derived.MetaCICNormalizationFrontierUp",
  "candidate_reason": "",
  "surface_classification": "",
  "load_bearing_score": 0,
  "hollow_risk_score": 0,
  "downstream_pressure_score": 0,
  "critical_path_score": 0,
  "verdict": "",
  "required_deepening": "",
  "acceptance_test": "",
  "suggested_lane": "",
  "verification_commands": []
}
```

`surface_classification` 取值：

```text
carrier_surface
route_ledger_surface
semantic_boundary
obstruction
endpoint
mixed
```

`verdict` 取值：

```text
keep
deepen
merge
demote
delete
block
```

`suggested_lane` 取值：

```text
paper
lean
paper_then_lean
human_review
no_action
```

## 评分

所有分数为 0 到 10 的整数。

### Load-bearing score

衡量内容是否证明或支撑了不可绕过的定理。

高分信号：

- consumer 不能绕过 boundary ledger；
- 某个闭合定理在以前需要条件的区域变成无条件；
- counterexample 阻止一个过强主张；
- theorem 被 consistency 或 closure endpoint 直接消费。

低分信号：

- 从 carrier 中投影字段；
- 重述 row membership；
- 包装已有 rows；
- 证明 `fields packet = [...]`；
- independence prose 只靠 tuple 长度。

### Hollow risk score

衡量内容形式上合法但理论上浅的风险。

高风险信号：

- theorem body 主要是 destruct carrier；
- 结论是输入字段的大 conjunction；
- 名字只含 `Carrier`、`Rows`、`Package`、`Surface`、`Obligations`、`Readiness`；
- 没有下游 theorem 引用；
- 附近没有 obstruction、exactness、no-bypass claim。

低风险信号：

- proof 使用 induction、inversion、route composition 或显式 contradiction；
- theorem 排除一类 bad consumer；
- theorem 减少 conditional endpoint 的假设；
- theorem 创建 endpoint 使用的 bridge。

### Downstream pressure score

衡量这个对象是否被别的内容必须使用。

高分信号：

- 被多个 concrete-instance 章节引用；
- 被 closurestatus target 消费；
- 用于 critical path theorem；
- paper-Lean bridge sync 依赖它。

低分信号：

- 没有 sibling reference；
- 没有 Lean imports 消费；
- 没有 endpoint consumer；
- 没有 conjecture 或 obstruction 依赖它。

### Critical path score

衡量到已知 endpoint 的距离。MetaCIC 和 Apophatic 试点目标只有在绑定具体 obligation 时才提高优先级。

## Verdict 语义

### keep

内容已经足够承重，不需要动作。

必须有：

- 至少一个 semantic boundary、obstruction 或 endpoint theorem；
- 没有未处理 hollow-risk；
- paper 和 Lean marker 审计通过。

### deepen

内容有用，但太浅。生成 deepening target。

常见深化方向：

- 加 no-bypass theorem；
- 证明 noninternalization；
- 证明某个条件定理在窄具体区域成立；
- 为过强 claim 给 counter-witness；
- 把章节连接到 endpoint theorem。

### merge

内容重复或只是另一个章节的弱变体，应合并到更强归属处。

merge target 必须写清：

- source chapter；
- target chapter；
- 要保留的 theorem label；
- 需要重定向的 label 或 reference；
- Lean namespace 落点。

### demote

内容有效，但不是 AI-origin primitive。它可以保留为基础设施，但不应计作原子发现。

典型情况：

- AI 章节只是既有 siblings 的组合；
- independence witness 只靠字段顺序；
- 没有唯一 consumer。

### delete

内容重复、无效或误导。除非是 paper/Lean 外的未引用生成物，否则需要人工确认。

### block

内容制造了虚假的闭合感，或隐藏未解决 obligation。相关分支在处理前不应继续扩张。

典型情况：

- paper claim 强于 Lean theorem；
- closurestatus 轴混淆；
- endpoint theorem 漏掉必要 hypothesis；
- AI-origin 章节缺少 nontriviality 或 field faithfulness。

## Deepening Target 格式

Deepening target 必须能被现有 paper / Lean 管线执行。

必填字段：

```json
{
  "kind": "ai_quality_deepening",
  "paper_files": [],
  "lean_files": [],
  "anchor": "",
  "problem": "",
  "required_theorem_shape": "",
  "forbidden_easy_paths": [],
  "acceptance_test": "",
  "verification_commands": []
}
```

好的 `required_theorem_shape` 示例：

```text
For every accepted ApophaticName carrier, any consumer route from the boundary
name to a value row factors through the displayed refusal ledger.
```

```text
For closed application subject reduction, prove the independent-codomain case
without the full AppArgTypeStable hypothesis.
```

```text
Show that digest sameness plus fiber membership does not imply source equality
without an exactness certificate.
```

坏目标示例：

```text
Add a NameCert package for X.
```

```text
Record the rows of X as a carrier.
```

```text
Add a theorem projecting the ledger field.
```

## 机械验证门

质量管线复用现有验证门，并只增加质量专用检查。

必须复用的现有命令：

```bash
cd lean4 && lake build
python3 tools/check-axioms.py
python3 lean4/scripts/bedc_ci.py audit
python3 lean4/scripts/bedc_ci.py axiom-purity --strict
cd papers/bedc && make check
```

质量专用检查：

- deepening target 必须命名一个被阻止的 bad inference 或 endpoint；
- 新 Lean theorem 不能只是 carrier projection；
- 新 paper theorem 不能只是解释性 prose；
- AI-origin 章节不能缺少 nontriviality story；
- review packet 必须分类内容层级；
- `deepen` verdict 必须提供 acceptance test。

## 实现计划

### Scanner

创建：

```text
papers/bedc/tools/auto-ai-quality/scan_ai_outputs.py
```

职责：

- 找出 AI-origin 章节；
- 将 chapter slug 映射到 Lean namespace；
- 按名字模式统计本地 Lean declarations；
- 读取 closurestatus grade；
- 检测 sibling references；
- 检测 downstream references；
- 输出 candidate JSON。

只读输入：

```text
papers/bedc/parts/concrete_instances/
lean4/BEDC/Derived/
lean4/scripts/critical_path.py output
docs/dossier/data/dependency.json if available
```

### Reviewer

创建：

```text
papers/bedc/tools/auto-ai-quality/review_candidate.py
```

职责：

- 读取 candidate JSON；
- 计算分数；
- 分类 surface layer；
- 输出 Markdown review packet；
- 当 verdict 为 `deepen` 时输出 deepening target。

第一版 reviewer 可以完全确定性。LLM review 后续只能作为 advisory layer，不作为唯一事实源。

### Board

创建：

```text
papers/bedc/tools/auto-ai-quality/BOARD.md
```

Board 只保存 deepening targets，不能变成新章节 discovery queue。

每个 card 包含：

- target id；
- chapter slug；
- verdict；
- required theorem shape；
- acceptance test；
- suggested lane；
- current status。

### Dispatcher

创建：

```text
papers/bedc/tools/auto-ai-quality/dispatch_target.py
```

职责：

- 选择一个未处理 deepening target；
- 渲染给现有 paper 或 Lean 自动化的 prompt；
- 标记 in progress；
- 验证后记录结果。

## 试点策略

第一阶段最多处理 20 个候选：

- 10 个 MetaCIC 候选；
- 10 个 Apophatic 候选。

成功标准：

- 至少 5 个 `deepen` target 转化为被接受的 Lean 或 paper 改动；
- 至少 2 个接受改动是 semantic boundary 或 obstruction theorem；
- 本管线不引入新的 AI-origin 章节；
- 不放松任何 build 或 audit gate；
- 不增加 unresolved paper-Lean marker drift。

## 示例 Review Packet

```json
{
  "id": "metacic-normalization-frontier-candidate-boundary",
  "chapter_slug": "metacicnormalizationfrontier",
  "origin": "ai",
  "paper_files": [
    "papers/bedc/parts/concrete_instances/5294_metacicnormalizationfrontier_namecert_construction.tex"
  ],
  "lean_files": [
    "lean4/BEDC/Derived/MetaCICNormalizationFrontierUp/TasteGate.lean"
  ],
  "primary_namespace": "BEDC.Derived.MetaCICNormalizationFrontierUp",
  "candidate_reason": "AI-origin frontier chapter with many route and boundary rows near the MetaCIC normalization endpoint.",
  "surface_classification": "route_ledger_surface",
  "load_bearing_score": 5,
  "hollow_risk_score": 6,
  "downstream_pressure_score": 7,
  "critical_path_score": 8,
  "verdict": "deepen",
  "required_deepening": "Prove that a closed-normal consumer cannot use the finished-normal endpoint without passing through candidate evidence or the displayed obstruction ledger.",
  "acceptance_test": "A new Lean theorem states a no-bypass property over the existing carrier rows and is cited by the paper immediately after the corresponding boundary theorem.",
  "suggested_lane": "lean",
  "verification_commands": [
    "cd lean4 && lake build",
    "python3 tools/check-axioms.py",
    "python3 lean4/scripts/bedc_ci.py audit",
    "python3 lean4/scripts/bedc_ci.py axiom-purity --strict"
  ]
}
```

## 操作原则

本管线保持以下不变量：

```text
AI 产物只有在携带依赖、阻止错误推理、或推进 endpoint 时，才计作理论进展。
```

其他内容可以作为基础设施保留，但不能被计入质量进展。
