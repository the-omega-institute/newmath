# BEDC 与 mathlib 桥接子论文

本子论文证明 BEDC 形式化对象与 mathlib 标准对象在精确定义的同构和保结构意义下对应。BEDC core 保持 mathlib-free 和 0-axiom 不变量不变；本桥接项目单向依赖 BEDC 与 mathlib，BEDC 主项目不导入本桥。

bridge 侧公开声明以 0-axiom 为硬标准，通过 Lean 编译期 guard 自动遍历 `BedcMathlibBridge.All` 覆盖的 Core / Adapter / Constructive surface。当前桥接实例清单以 `MATRIX.md` 为真实源，本 README 不缓存清单。
