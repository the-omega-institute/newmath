# HOW_INCREMENT_WORKS

## 目标

本文件规定 BEDC 下一次理论增量的追加方式。适用对象包括 `v1.5.6`、`v1.6`、`v2.0` 及其后续增量。规则是 append-only：新增内容进入新章节或新主题，不在无迁移记录的情况下静默改写既有活跃结论。

## 1. 放置新章节

- 如果增量属于已有主题，把新的 `\chapter` 文件放到 `parts/<theme>/` 下。
- 已有主题的 wrapper 文件保持版本无关命名，例如 `parts/proof_obligations.tex`、`parts/concrete_hardening.tex`。
- 如果增量引入全新主题，新建 `parts/<new_theme>/` 目录，并新增 `parts/<new_theme>.tex` wrapper。
- `main.tex` 只输入主题 wrapper，不直接输入一串按版本编号排列的增量文件。

## 2. 注册 claim_id

- 每个新的章节级 `\label{ch:...}` 都必须在 `papers/bedc/claim-registry.md` 新增一行。
- claim_id 统一使用 `bedc:<theme>:<concept-slug>`。
- `granularity` 必须显式写明：`chapter`、`section`、`theorem`、`definition`、`predicate` 之一。
- 如果一个旧章节在新增量中被细化但保留可引用地位，migration 说明写进 `01_migration_index.tex`，claim-registry 保留旧条目并增加新条目，不覆盖旧 claim_id。

## 3. 增加 Lean 目标

- 在 `lean4/BEDC/` 下为新对象选择对应模块；若现有模块不合适，再新增模块。
- 先放入最小载体：需要的 `axiom` carrier、关系、结构或 predicate。
- 然后加入同名 theorem target，允许先写 `:= by sorry`，但 theorem 名称必须稳定。
- 新 theorem 名称需要同步写入 `papers/bedc/correspondence.md`，把 paper label、lean target、当前状态三者对齐。
- 每次 `claim-registry.md` 增加 theorem/predicate 级条目时，Lean 侧必须存在对应 target，不允许只在论文里出现。

## 4. 更新 governance 状态

- `papers/bedc/frontmatter/status.tex` 记录当前活跃状态，不是历史快照仓库。
- 新增量如果改变活跃 contract，需要在 `status.tex` 中新增或更新对应行。
- 更新状态时必须保留旧状态与新状态的可比性：先写当前活跃对象，再写新增的 policy / proof target / deferred obligation。
- 如果一个对象从 `Deferred` 变成 `Active` 或 `ProofTarget` 变成 `Checked`，在 `01_migration_index.tex` 写明 supersession。

## 5. 增加 migration note

- 每个会改变活跃读取方式的增量，都在 `papers/bedc/parts/project_governance/01_migration_index.tex` 增加一条表项或补充小节。
- 记录格式至少包含四列：
  - earlier location
  - issue
  - current refinement
  - status (`Refined` / `Deprecated` / `Deferred`)
- 如果只是补证明、不改活跃解释，可不加大表项；但若改变读者应引用的章节、关系或 theorem，必须登记。

## 6. 更新 paper ↔ Lean correspondence

- 当一个 `axiom` 变成可用 theorem，或一个 `sorry` 变成 checked proof，必须同步更新 `papers/bedc/correspondence.md` 的 `status`。
- 如果 Lean target 名称变化，先在论文中补新 label / 新 claim_id，再更新 correspondence；不要只改单侧。
- 如果一个 paper-level predicate 后来被拆成多个 Lean theorem，保留原 claim_id 作为聚合入口，并为新增 theorem 分配新的 theorem/predicate 级 claim_id。

## 7. 验证顺序

- 先改论文与 registry。
- 再加 Lean target。
- 再改 `status.tex` / `01_migration_index.tex` / `correspondence.md`。
- 最后运行：
  - `cd lean4 && lake build`
  - `cd papers/bedc && make`

## 8. 禁止事项

- 不恢复按版本后缀命名的 `parts/..._v1_5_x/` 目录。
- 不把 migration 说明写进章节正文里替代 governance 记录。
- 不在没有 claim_id、没有 label、没有 Lean target 的情况下新增活跃 theorem 叙述。
