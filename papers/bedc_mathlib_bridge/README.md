# BEDC 与 mathlib 桥接子论文

本子论文证明 BEDC 形式化对象与 mathlib 标准对象在精确定义的同构和保结构意义下对应。BEDC core 保持 mathlib-free 和 0-axiom 不变量不变；本桥接项目单向依赖 BEDC 与 mathlib，BEDC 主项目不导入本桥。

bridge 侧公开声明以 0-axiom 为硬标准，通过 Lean 编译期 guard 自动遍历 `BedcMathlibBridge.All` 覆盖的 Core / Adapter / Constructive surface。当前桥接实例清单以 `MATRIX.md` 为真实源，本 README 不缓存清单。

## 导出 witness 与 hard gates

一个 constructive adequacy 行声称“已导出”时，必须在 bridge 侧提供薄 witness record。record 的字段类型就是该 anchor 固定签名的精确命题；实例只引用已存在的 0-axiom witness。Gate S 锁定 witness record 的字段名与 projection type hash，防止把签名弱化后仍让矩阵通过。Gate D 从 `MATRIX.md` 的 `bedc-bridge-row` metadata 读取 `export_witness`，再让 Lean 检查声明存在、类型由 record 固定、`collectAxioms` 为空，并与 bridge 侧 witness registry 一一对应。

Int exported witness 的 ring/order/divisibility slot 绑定同一个 canonical `CInt.toInt`/`CInt.ofInt` surface；`ring_apply`、`add_apply`、`mul_apply`、`order_apply`、`dvd_apply` 都是 concrete wrapper theorem 对应的 record 字段，受 Gate S 与 Gate D 同时约束。

`MATRIX.md` 使用四类客观分类：`exported_core`、`subsumed_by_core`、`measured_boundary`、`out_of_scope_generic`。Int bridge 的 Gate D 由 Lean 枚举声明的 Int import surface 中 typeclass result 形如 `C Int` 的实例，按 structure parent DAG 去重到极大类；每个极大类必须恰好有一个分类行。该 import surface 明确包含 `Mathlib.Data.Int.ConditionallyCompleteOrder`，所以条件完备序及其 `SupSet`/`InfSet` 投影在枚举和 MATRIX 中可见。额外 axiom-footprint measurement row 可设置 `classification:false`，只进入 Gate E，不作为 Gate D 的唯一分类。

接入一个 anchor 的步骤：在 `lean4/BedcMathlibBridge/Export/<Anchor>.lean` 定义 `<Anchor>ExportWitness` 和具体 witness；把 0-axiom export 文件纳入 `BedcMathlibBridge.Export` 与 `BedcMathlibBridge.All`；把 witness 加入 `BedcMathlibBridge.CI.ExportAudit.exportWitnessRegistry`；在 `MATRIX.md` 行内写稳定 `row_id`、四分类、`mathlib_class`、`mathlib_instance` 与 `export_witness` metadata；运行 Gate A/D/S。

boundary fact 行不写桥定理。Gate E 从 `MATRIX.md` 读取 `boundary_decl` 与排序后的 `expected_axioms`，对实际 declaration 运行 `collectAxioms` 并精确比对，同时拒绝 hard-forbidden axioms。`BedcMathlibBridge.Audit.BoundaryFactAxiomGuard` 不被 `BedcMathlibBridge.All` import，避免 classical footprint 污染 bridge surface。

当前 Int replacement probe 的结论以 `MATRIX.md` 和 Gate E 实测为准：canonical CInt add/mul/order/dvd wrappers 保持 0-axiom export；bundled CommRing/EuclideanDomain 的 from-scratch replacement probe 使用 term-mode 证明后仍有残留公理 footprint，因此诚实记录为 measured boundary，而不作为 exported witness。
