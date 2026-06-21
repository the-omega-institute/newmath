# bedc_mathlib_bridge 工作规范 (薄)

> 全局规范看仓库根 `CLAUDE.md`; 本桥的目标成果看同目录 `GOAL.md`. 这里只加桥特有的硬规则, 不复述.

桥是**校准证书**, 不是造数学的地方. 数学属于 `lean4/BEDC/`; 桥只记 `BEDC对象 | mathlib目标 | tier | 定理 | axiom账本 | 边界` 一行.

## 四条硬规则

1. **BEDC 一侧必须是 BEDC 自己的对象.** 桥的 BEDC 侧结构 (carrier / 运算 / 关系, 如 `bwordLength`/`append`、`NatMul`、`NatUnaryPrefix`、`IntPairClassifier`) 必须取自 BEDC; mathlib 只是**对照目标**, 永远不是 BEDC 侧结构的来源. **禁止** `ofX (运算 (toX a) (toX b))` 这类把 mathlib 运算拉回冒充 "BEDC 的运算" (structure-grafting = laundering). 加法用 BEDC `append`↔`Nat.add`, 乘法就得用 BEDC `NatMul`↔`Nat.mul`, 序用 BEDC `NatUnaryPrefix`, 对称. Gate B 只证明登记的 BEDC primitive 出现在 value 依赖图里, 可防忘登记和无依赖 graft, 但这是必要非充分条件: 它不能证明没有死 anchor, 也不能证明没混入 mathlib 运算; 机器 gate 不等于完整语义诚实证明, 语义保真仍靠对象自己的 adequacy theorem 和 review.

2. **BEDC 缺的, 记成 BEDC 缺口写回 BEDC, 不在桥里补造.** 若桥需要的 BEDC 对象不存在: **不**用 mathlib 顶替, 也**不**在桥里把它造出来冒充 BEDC 声明. 在 `MISSING_IN_BEDC.md` 记一行 (缺的对象 + 桥哪行需要它 + 该归 BEDC 哪章), 该 matrix 行标 `blocked-on-bedc`; 真正的构造写进 `lean4/BEDC/`. 桥保持薄, 缺口薄呈现.

3. **bridge surface 0-axiom.** `BedcMathlibBridge.All` 覆盖的 Core / Adapter / Constructive surface 每条公开声明 `#print axioms` 必须空 (`scripts/check_bridge_axioms.py` + `Audit/BridgeAxiomGuard.lean` 自动审, 加新定理自动纳入). 触 `Classical.choice`/`Quot.sound`/`propext` 的声明不得进入该 surface, **绝不假装 0-axiom**.

4. **单向 + 薄.** `lean4/BEDC/**` 永不 import Mathlib 或本桥 (`scripts/check_no_back_edge.py` 守). 不在桥里堆数学; 每个对象一行 matrix, 不复制事实正文.
