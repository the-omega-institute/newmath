# BEDC 与 mathlib 桥接子论文

本子论文证明 BEDC 形式化对象与 mathlib 标准对象在精确定义的同构和保结构意义下对应。BEDC core 保持 mathlib-free 和 0-axiom 不变量不变；本桥接项目单向依赖 BEDC 与 mathlib，BEDC 主项目不导入本桥。

constructive tier 的定理以 0-axiom 为硬标准，通过 `#print axioms` 检查。后续 classical tier 中依赖选择、公理化实数或商构造的对象会显式标注 axiom 预算。当前实例是 BEDC 的 `BMark` 与 mathlib/Lean 的 `Bool` 的 constructive 等价。
