# BEDC 与 mathlib 桥接子论文

本子论文证明 BEDC 形式化对象与 mathlib 标准对象在精确定义的同构和保结构意义下对应。BEDC core 保持 mathlib-free 和 0-axiom 不变量不变；本桥接项目单向依赖 BEDC 与 mathlib，BEDC 主项目不导入本桥。

bridge 侧公开声明以 0-axiom 为硬标准，通过 Lean 编译期 guard 自动遍历 `BedcMathlibBridge.All` 覆盖的 Core / Adapter / Constructive surface。当前桥接实例清单以 `MATRIX.md` 为真实源，本 README 不缓存清单。

## 导出 witness 与 hard gates

一个 `exported_core` 行声称“已导出”时，必须在 bridge 侧提供薄 witness record 和 mathlib correspondence 定理。record 的字段类型就是该 anchor 固定签名的精确命题；实例只引用已存在的 0-axiom witness。Gate S 锁定 witness record 的字段名与 projection type hash，防止把签名弱化后仍让矩阵通过。Gate D 从 `MATRIX.md` 的 `bedc-bridge-row` metadata 读取 `export_witness`，再让 Lean 检查声明存在、类型由 record 固定、`collectAxioms` 为空，并与 bridge 侧 witness registry 一一对应。Gate W 读取 `mathlib_correspondence_decl`、`bedc_irreducible_decl` 与 `mathlib_decl`，要求 correspondence 声明存在、无公理、类型非平凡，并同时引用 BEDC anchor 与 mathlib anchor。

Int exported witness 的 ring/order/divisibility slot 绑定同一个 canonical `CInt.toInt`/`CInt.ofInt` surface；`ring_apply`、`add_apply`、`mul_apply`、`order_apply`、`dvd_apply` 都是 concrete wrapper theorem 对应的 record 字段，受 Gate S 与 Gate D 同时约束。

`MATRIX.md` 使用五类客观分类：`exported_core`、`bedc_constructive_core`、`subsumed_by_core`、`measured_boundary`、`out_of_scope_generic`。`exported_core` 是强层：BEDC 侧 0-axiom witness 已存在，并有已编译的 mathlib correspondence 定理。`bedc_constructive_core` 是中间层：BEDC 内部 0-axiom witness 已存在，mathlib correspondence 不在该行声称，`mathlib_correspondence_decl` 必须留空。Int bridge 的 Gate D 由 Lean 枚举声明的 Int import surface 中 typeclass result 形如 `C Int` 的实例，按 structure parent DAG 去重到极大类；每个极大类必须恰好有一个分类行。该 import surface 明确包含 `Mathlib.Data.Int.ConditionallyCompleteOrder`，所以条件完备序及其 `SupSet`/`InfSet` 投影在枚举和 MATRIX 中可见。额外 axiom-footprint measurement row 可设置 `classification:false`，只进入 Gate E，不作为 Gate D 的唯一分类。

Gate H 是 anti-hollow 语法闸，扫描 `MATRIX.md` 中 `exported_core` / `bedc_constructive_core` 指向的声明以及 bridge `Export/` surface，拒绝已知可语法识别的空壳形态：`*_Statement` / `*_well_formed` 伴随 `True.intro` 或 `trivial`、certificate-like hypothesis 导出 existential 结论，以及纯 hypothesis projection 伪造 existential witness。此闸不声称判定任意定理是否有数学内容；通用 vacuity 不可判定，Gate W 的 mathlib correspondence 仍是 `exported_core` 的主防线，Gate H 只是 `bedc_constructive_core` 层的纵深防御。默认 allowlist 为空，任何豁免必须在 checker 中带理由登记。

接入一个强 anchor 的步骤：在 `lean4/BedcMathlibBridge/Export/<Anchor>.lean` 定义 `<Anchor>ExportWitness`、具体 witness 与 mathlib correspondence 定理；把 0-axiom export 文件纳入 `BedcMathlibBridge.Export` 与 `BedcMathlibBridge.All`；把 witness 加入 `BedcMathlibBridge.CI.ExportAudit.exportWitnessRegistry`；在 `MATRIX.md` 行内写稳定 `row_id`、分类、`mathlib_class`、`mathlib_instance`、`mathlib_decl`、`bedc_irreducible_decl`、`export_witness` 与 `mathlib_correspondence_decl` metadata；运行 Gate A/D/S/W。BEDC 内部构造若没有 correspondence 定理，使用 `bedc_constructive_core`，不写强 export claim。

boundary fact 行不写桥定理。Gate E 从 `MATRIX.md` 读取 `boundary_decl` / `mathlib_decl` 与排序后的 `expected_axioms` / `mathlib_footprint`，对实际 declaration 运行 `collectAxioms` 并精确比对，同时拒绝 hard-forbidden axioms。每行的 `bedc_irreducible_footprint` 还必须用 `axiom_status` 逐公理分类：`eliminated` 不能残留在 footprint 中，残留项只能是 `mathlib_intrinsic`、`structural_quotient` 或 `principled_irreducible`。`choice_status` 保留为 `Classical.choice` 的兼容字段。每行可带 `place`、`locatedness`、`quotient_status` metadata；缺省为 `n_a`，枚举值由 `scripts/matrix_metadata.py` 校验。`BedcMathlibBridge.Audit.BoundaryFactAxiomGuard` 不被 `BedcMathlibBridge.All` import，避免 classical footprint 污染 bridge surface。

当前 Int replacement probe 的结论以 `MATRIX.md` 和 Gate E 实测为准：canonical CInt add/mul/order/dvd wrappers 保持 0-axiom export；残留 `propext` 是 mathlib bundled class / packaged lemma 的 footprint，记为 `mathlib_intrinsic`；Euclidean probe 中可消的 `Quot.sound` 已通过避开 mathlib abs-wrapper lemma 从 BEDC irreducible footprint 中移除；条件完备性的 `Classical.choice` 是 arbitrary-set sup/inf 的 Prop-to-Type 选择，记为 `principled_irreducible`。无可消公理被藏成 gap。

mathlib 的实数任意上确界 / 条件完备序，以及 p 进整数和 p 进数的公开结构，在 `MATRIX.md` 中作为 measured boundary 记录。实测 footprint 为 `Classical.choice`、`Quot.sound`、`propext`，即 mathlib 侧经 Cauchy quotient 与 choice；BEDC canonical CZp / CQp 与 located-sup 替代是 0-axiom 目标，此矩阵不构造、不声称。`infinite_archimedean` 上的 `located` / `arbitrary` 只是 harness tag，不是把无穷位写成数论 prime 的 Lean 定理。
