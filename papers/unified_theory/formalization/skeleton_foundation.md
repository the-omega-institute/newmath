# PZG-BEDC 内核理论形式化逻辑骨架

来源文档: `papers/unified_theory/PZG_BEDC_kernel_formal.md`。

目的: 为隔离的 Lean4 + mathlib 形式化项目抽取逻辑骨架。本文只描述对象、依赖、账本状态与形式化可行性,不把数值窗口或开放桥伪装成全称证明。

## Part A - 全文高层索引

按文档实际结构列出第〇章至第三十章。

| 章 | 标题 | 核心 object / 定理编号 | 主账本状态 |
|---|---|---|---|
| 第〇章 | 内核总对象 | 定义 0.1: `𝒦 = (𝖧, 𝖦, σ, 𝒜, 𝒯, 𝖹, 𝖣, 𝖭, ℛ, 𝖱, 𝖫, 𝖲, Φ, π, K_∞, Σ_∞, ^, Θ, Prop, Cert, Ont)` | 〔定义〕; 作为后文载荷定理的总接口 |
| 第一章 | 最小二分与交换 | 定义 1.1-1.2: 标记 `0,1` 与交换 `σ` | 〔定义〕; 载荷在定理 16.4 |
| 第二章 | 历史、事件与生成公理 | 定义 2.1-2.3, 公理 A1-A2, 命题 2.4-2.5 | 基础结构为〔定义〕/〔公理〕; 拼接与有限深度〔closed〕 |
| 第三章 | 单位性判据 | 定义 3.1, 定理 3.2 | 终止 + 局部合流推出唯一标准形〔closed〕 |
| 第四章 | 素数轴与唯一分解 | 定义 4.1, 定理 4.2-4.5 | 素分解、自由交换幺半群、Euclid 逃逸全为〔closed〕 |
| 第五章 | Zeckendorf 尺度与 PZG 双射 | 定义 5.1/5.4, 引理 5.2, 定理 5.3/5.5-5.7 | Zeckendorf、PZG 双射、归一化、进位终止为〔closed〕; 5.3 证明附窗口核验 |
| 第六章 | 规范载荷:自相似双面 | 定理/命题 6.1-6.59, 定义 6.4 | 基础代数与组合多为〔closed〕; 大量条目含窗口证书、解析层引注; O-5 对角回传仍〔open〕 |
| 第七章 | 本体同一性判据:总代码 | 定义 7.1, 判据 7.2, 定理 7.3 | 总代码判据为〔semantic〕; 无隐形寄存器为〔closed·定义性〕 |
| 第八章 | 有限读数与窗口 | 定义 8.1-8.2, 定理 8.3-8.5, 推论 8.6 | 有限读数、CRT、鸽巢纤维为〔closed〕 |
| 第九章 | 读数分类范例:二轴范数 | 引理/命题/定理 9.1-9.10 | 两平方分类全链〔closed〕; 依赖 FTA、Wilson、Thue、Brahmagupta |
| 第十章 | 对偶完成:隐藏纤维与 solenoid | 定义 10.1, 定理 10.2-10.10 | `Ẑ ≅ ∏p ℤ_p`, `Ẑ^∨ ≅ ℚ/ℤ`, `Σ_∞^∨ ≅ ℚ` 皆〔closed〕; 10.5 拓扑对偶曾列 O-4,后由 20 章闭合 |
| 第十一章 | residual 与四状态账本 | 定义 11.1-11.3 | 账本四状态为〔定义〕 |
| 第十二章 | tail 演算 | 定义 12.1-12.2, 范例 12.3, 定理 12.4/12.6, 推论 12.5 | tail 预算与计算证书规则〔closed〕 |
| 第十三章 | 账本纪律与守恒 | 纪律公理 D, 定理 13.1-13.2 | D 为〔公理·义务〕; 条件守恒与可证伪半闭合〔closed〕 |
| 第十四章 | 自编码 | 定义 14.1, 定理 14.2, 原则 14.3 | PZG-Gödel 自编码〔closed〕; 语法/语义边界〔semantic〕 |
| 第十五章 | 机器层:事件即指令 | 定义 15.1-15.2, 机器公设 U | ISA/Sub 为〔定义/构造〕; U 属〔公理·构造性; open 账 O-1〕 |
| 第十六章 | 不动点与对角三定理 | 定理 16.1-16.4 | 不动点与闭合判定不可达条件于 U; 对角超出与 σ 载荷〔closed〕 |
| 第十七章 | 性质提升公理与内化塔 | 定义 17.1/17.5, 公理 17.2, 定理 17.3-17.4/17.8, 命题 17.6, 范例 17.9 | 有限生成类继承无条件闭合; 一般性质提升条件于 U; 逐层算术化 O-2 仍 open |
| 第十八章 | 状态、素数地址与时间之矢 | 定义 18.1/18.2/18.6/18.9, 定理 18.3-18.5/18.7/18.8/18.10/18.11, 推论 18.12 | 素数地址、码账协变、时间之矢、群化与成本时间〔closed〕 |
| 第十九章 | 相位与酉性线 | 定义 19.1-19.2, 定理 19.3/19.5/19.6, 推论 19.4 | `Re s = 1/2` 的酉性刻画〔closed〕; 双面相位含窗口证书 |
| 第二十章 | 可见-隐藏动力学 | 定义 20.1/20.5/20.8, 规格 20.2, 定理 20.3/20.6/20.10/20.12, 推论 20.4/20.7/20.11, 命题 20.14 | 隐藏刚性、喉部 cocycle、流线定理、紧致性〔closed〕; 平滑规格为〔semantic〕 |
| 第二十一章 | 从最小核到传统对象 | 路线 21.1, 定义 21.3 | 数系生成路线〔closed; 良定性依范式〕; 导数为核内谓词定义 |
| 第二十二章 | 热迹与 Euler 判据 | 定义 22.1/22.4, 定理 22.2/22.3/22.5, 推论 22.6 | zeta 热迹、Euler 乘积、带标签向量不灭〔closed〕; Hilbert 幺半群反例有窗口证书 |
| 第二十三章 | 完成化契约与反射 | 契约 23.1, 定义 23.2/23.5, 定理 23.3/23.4/23.6/23.7/23.9/23.10, 命题 23.8, 推论 23.11 | C3a 与解析机器四石闭合; 规格为〔semantic〕; O-9 已闭合 |
| 第二十四章 | 零点账本 | 定义 24.1/24.2/24.7, 定理 24.3-24.5/24.8/24.9/24.11, 推论 24.6/24.12, 账目 24.10 | 本地账、镜像配对、零点 tail 本性多为〔closed〕; RH 桥 24.10 为〔open; O-6〕 |
| 第二十五章 | 谱几何层:中线的第三刻画 | 定义 25.1, 定理 25.2-25.7/25.10-25.13, 推论 25.6/25.11 | 范数律、ℓ² 边界、酉流、再生核、中线三重刻画〔closed〕; Hardy/HP 边界为 semantic 引注 |
| 第二十六章 | 桥通道:显式公式的账本形式 | 定义 26.1, 命题 26.2/26.7, 定理 26.3/26.5, 账目 26.4, 条目 26.9-26.10 | 显式公式和散射形式〔closed·解析层〕; 正性桥 O-6 仍〔open〕 |
| 第二十七章 | 有限窗口与无穷 | 定理 27.1-27.3, 评注 27.4-27.42 | 有限窗口/tail 与两座塔对照〔closed〕; RH、全知、物理词典多为〔semantic·前沿引注〕 |
| 第二十八章 | 内核主定理 | 定理 28.1-28.2, 推论 28.3, 评注 28.4-28.5 | 主结构逐条指针〔closed〕; 分类张力与因果定位为〔semantic〕 |
| 第二十九章 | 开放账本 | O-1 至 O-10, 评注 29.1-29.8 | O-1/O-2/O-5/O-6/O-10 为 open; O-3/O-4/O-7/O-8/O-9 为 closed; 物理/几何对照为 semantic |
| 第三十章 | 最终压缩 | 全理论压缩句 | 当前态综合; 最后一条核心开放项为 RH/正性桥 |

## Part B - 基础层深骨架

范围: 第〇章、第一部 ch1-3、第二部 ch4-6。这里按要求列出定义、公理、命题、定理、引理、推论。`depends_on` 只列证明或陈述直接用到的核心前件。

### 第〇章

- id: 定义 0.1
  kind: definition
  status: 〔定义〕
  statement: 内核对象 `𝒦` 是由历史、生成、交换、素数指数状态、PZG 编码/解码/归一化、重整化、读数、账本、自代码、相位、隐藏纤维、完成化、反射、性质/证书/对象化等分量组成的有序结构。
  depends_on: []
  formalization_note: structural/inductive; 最适合作为 Lean `structure KernelComponents` 或分阶段 typeclass/structure 接口,各字段先占位为类型、函数或谓词。
  formalizable_phase1: yes - 可先形式化字段级骨架,不要求一次性证明每个字段载荷。

### 第一章

- id: 定义 1.1
  kind: definition
  status: 〔定义〕
  statement: 取两个基本标记 `0` 与 `1`,它们仅表示最小二分而非自然数。
  depends_on: []
  formalization_note: structural/inductive; Lean 中可用 `inductive Mark | zero | one`。
  formalizable_phase1: yes - 两构造子枚举型直接可形式化。

- id: 定义 1.2
  kind: definition
  status: 〔定义〕
  statement: 交换 `σ` 在两个标记上互换 `0` 与 `1`,且是标记层唯一原始非平凡操作。
  depends_on: [定义 1.1]
  formalization_note: structural/inductive; 定义为 `swap : Mark -> Mark`,并可证明 `swap_involutive` 与非平凡性。
  formalizable_phase1: yes - 显式模式匹配即可。

### 第二章

- id: 定义 2.1
  kind: definition
  status: 〔定义〕
  statement: 标记历史由空历史 `e` 与扩张 `E_0,E_1` 有限生成,长度为扩张次数,拼接由右参数递归定义并以 `e` 为右单位。
  depends_on: [定义 1.1]
  formalization_note: structural/inductive; Lean 中用 `inductive MarkHist | empty | ext Mark MarkHist` 与递归定义 `append`。
  formalizable_phase1: yes - 结构归纳天然给出长度与拼接性质。

- id: 定义 2.2
  kind: definition
  status: 〔定义〕
  statement: 生成事件是四元组 `(src, op, arg, tag)`,其中 `src` 是来源历史、`op` 是内核指令、`arg` 是输入码、`tag` 是输出标记。
  depends_on: [定义 1.1, 定义 2.1, 定义 15.1]
  formalization_note: structural/inductive; phase 1 可把 `op` 抽象为参数类型或有限枚举,不展开第十五章运行语义。
  formalizable_phase1: partial - 事件记录可形式化,但完整 ISA 语义属于后续层。

- id: 定义 2.3
  kind: definition
  status: 〔定义〕
  statement: 事件历史是生成事件的有限序列,生成算子 `𝖦(h,u)=h∗u` 将事件接续到历史之后。
  depends_on: [定义 2.1, 定义 2.2]
  formalization_note: structural/inductive; 可用 `List Event` 或自定义 inductive,生成算子为 `List.snoc`/递归 append。
  formalizable_phase1: yes - 有限序列和接续可直接形式化。

- id: 公理 A1
  kind: axiom
  status: 〔公理〕
  statement: 若历史性质 `P` 在空历史成立且对任意事件扩张保持,则 `P` 对一切历史成立;标记扩张是原子生成事件的特例。
  depends_on: [定义 2.1, 定义 2.3]
  formalization_note: structural/inductive; 在 Lean 中不应作为 axiom,而应由历史的 inductive recursor/induction principle 实现。
  formalizable_phase1: yes - 改写为归纳原理后由 kernel 自动给出。

- id: 公理 A2
  kind: axiom
  status: 〔公理〕
  statement: 每条历史只含有限多事件。
  depends_on: [定义 2.3]
  formalization_note: structural/inductive; 若历史定义为 `List Event`,该性质由类型保证,无需公理。
  formalizable_phase1: yes - 有限性随 `List`/inductive 编码自动成立。

- id: 命题 2.4
  kind: prop
  status: 〔closed〕
  statement: 历史拼接满足结合律,且空历史 `e` 是左右单位。
  depends_on: [定义 2.1, 公理 A1]
  formalization_note: structural/inductive; 对递归定义的 append 做结构归纳即可。
  formalizable_phase1: yes - Lean 中是典型 list/inductive append monoid 证明。

- id: 命题 2.5
  kind: prop
  status: 〔closed〕
  statement: 任何证书只引用有限多生成事件。
  depends_on: [公理 A2]
  formalization_note: structural/inductive; 若 `Cert` 被编码为历史或有限列表,有限深度由编码直接推出。
  formalizable_phase1: yes - phase 1 可先把证书定义为历史别名或结构字段。

### 第三章

- id: 定义 3.1
  kind: definition
  status: 〔定义〕
  statement: 重写系统是历史上的二元关系;标准形无后继;终止表示无无穷链;局部合流表示任意一步分叉可经多步重写汇合。
  depends_on: [定义 2.1]
  formalization_note: structural/inductive; Lean 中定义 relation、reflexive transitive closure、normal form、well-founded/terminating、local confluence。
  formalizable_phase1: yes - mathlib 提供关系传递闭包与 well-founded 工具。

- id: 定理 3.2
  kind: theorem
  status: 〔closed〕
  statement: 任一终止且局部合流的重写系统中,每条历史恰有一个标准形。
  depends_on: [定义 3.1, 公理 A1]
  formalization_note: structural/inductive; 这是 Newman's lemma 的具体形态,可用 well-founded induction 证明或倚 mathlib 关系库。
  formalizable_phase1: yes - 非平凡但适合 phase 1,可作为通用 rewriting lemma。

### 第四章

- id: 定义 4.1
  kind: definition
  status: 〔定义〕
  statement: 用单标记历史实现自然数、加法、乘法、序、带余除法和素数谓词;`n>1` 为素当且仅当任一分解 `n=ab` 迫使一因子为 `1`。
  depends_on: [定义 2.1, 公理 A1]
  formalization_note: number-theoretic; 在 mathlib 项目中应映射到 `Nat`, `Nat.Prime`, `Nat.factorization`,而不重建所有算术。
  formalizable_phase1: partial - 文档的 first-principles 实现可作为注释层,Lean+mathlib 中建议用现成自然数理论。

- id: 定理 4.2
  kind: theorem
  status: 〔closed〕
  statement: 每个大于 `1` 的自然数都可表示为有限个素数的乘积。
  depends_on: [定义 4.1, 公理 A1]
  formalization_note: number-theoretic; mathlib 中由自然数唯一分解或 factorization 支撑。
  formalizable_phase1: yes - 可用 `Nat.exists_prime_and_dvd`/factorization 路线实现。

- id: 定理 4.3
  kind: theorem
  status: 〔closed〕
  statement: 自然数的素分解在重排意义下唯一。
  depends_on: [定义 4.1, 定理 4.2]
  formalization_note: number-theoretic; mathlib 的 `Nat.factorization` 给出唯一指数函数,比手写最小反例证明更稳。
  formalizable_phase1: yes - 作为后续 PZG 的核心依赖,优先形式化为 factorization 唯一性。

- id: 定理 4.4
  kind: theorem
  status: 〔closed〕
  statement: 正自然数乘法幺半群是素数轴上的自由交换幺半群,且每个素指数读数 `v_p` 对乘法加性。
  depends_on: [定理 4.2, 定理 4.3]
  formalization_note: number-theoretic; 可用 `Nat.factorization_mul`、有限支撑函数和 free commutative monoid 等价表述。
  formalizable_phase1: yes - 是 PZG 编码和动力学地址原则的基础定理。

- id: 定理 4.5
  kind: theorem
  status: 〔closed〕
  statement: 对任意有限素数集 `S`,Euclid 逃逸数 `∏_{p∈S} p + 1` 对每个 `p∈S` 余 `1`,因此其素因子不在 `S` 中。
  depends_on: [定理 4.2, 定理 4.3]
  formalization_note: number-theoretic; 有限乘积、模同余和素因子存在即可。
  formalizable_phase1: yes - mathlib 支持有限集合乘积和整除同余。

### 第五章

- id: 定义 5.1
  kind: definition
  status: 〔定义〕
  statement: Fibonacci-like 序列取 `F₀=1,F₁=1,F₂=2,F_{k+2}=F_{k+1}+F_k`。
  depends_on: []
  formalization_note: number-theoretic; 可定义递归函数并与 mathlib Fibonacci 做索引换算。
  formalizable_phase1: yes - 简单递归定义。

- id: 引理 5.2
  kind: lemma
  status: 〔closed〕
  statement: 交错下标和 `F_k+F_{k-2}+F_{k-4}+...` 等于 `F_{k+1}-1`。
  depends_on: [定义 5.1]
  formalization_note: number-theoretic; 对 `k` 做强归纳或按奇偶拆分求和。
  formalizable_phase1: yes - 作为 Zeckendorf 唯一性的核心估计。

- id: 定理 5.3
  kind: theorem
  status: 〔closed〕
  statement: 每个 `n≥0` 唯一表示为无相邻 `1` 的 Fibonacci 位和 `Σ u_k F_k`。
  depends_on: [定义 5.1, 引理 5.2]
  formalization_note: number-theoretic; 证明可用贪心存在性 + 区间划分唯一性; 文中窗口核验只作辅助,不应替代证明。
  formalizable_phase1: yes - 非平凡但核心,可先形式化合法词、decode 与区间覆盖。

- id: 定义 5.4
  kind: definition
  status: 〔定义〕
  statement: PZG 位表 `z=(z_{p,k})` 在每个素轴上是无相邻 `1` 且全局有限支撑的位表,轴指数 `e_p(z)=Σ_k z_{p,k}F_k`,解码为 `𝖣(z)=∏_p p^{e_p(z)}`。
  depends_on: [定义 5.1, 定理 4.4]
  formalization_note: structural/inductive; 用 `Finsupp` 表示素数到有限合法词或素数-位二维有限支撑。
  formalizable_phase1: yes - 需要先选定合法词数据结构。

- id: 定理 5.5
  kind: theorem
  status: 〔closed〕
  statement: PZG 解码 `𝖣 : 𝖹 -> ℕ_{≥1}` 是双射。
  depends_on: [定理 4.4, 定理 5.3, 定义 5.4]
  formalization_note: number-theoretic; 由素因子指数唯一性与逐轴 Zeckendorf 唯一性组合。
  formalizable_phase1: yes - 是 phase 1 的中心目标之一。

- id: 定理 5.6
  kind: theorem
  status: 〔closed〕
  statement: 位表逐位相加后逐素轴存在唯一合法归一化 `𝖭(z+w)`,且解码把归一化加法送到整数乘法: `𝖣(𝖭(z+w))=𝖣(z)·𝖣(w)`。
  depends_on: [定理 4.4, 定理 5.3, 定理 5.5]
  formalization_note: number-theoretic; 归一化可定义为对指数和重新取 Zeckendorf 表示。
  formalizable_phase1: yes - 不必先实现具体进位算法,可先定义规范化函数并证明乘法性。

- id: 定理 5.7
  kind: theorem
  status: 〔closed〕
  statement: Zeckendorf 后继进位链有限终止,步数不超过最高指标。
  depends_on: [定理 5.3]
  formalization_note: structural/inductive; 若按重写规则证明,需定义具体 carry relation 和下降度量。
  formalizable_phase1: partial - 可先用定理 5.3 的规范化存在性避开算法终止,后续再证明进位重写终止。

### 第六章

- id: 定理 6.1
  kind: theorem
  status: 〔closed〕
  statement: 任意两个忠实数字规范之间由解码合成得到位词双射,只经解码分解的性质不依赖规范选择。
  depends_on: [定理 5.5]
  formalization_note: structural/inductive; 需抽象 `FaithfulNumeralSystem` 为与 `ℕ` 等价的编码。
  formalizable_phase1: yes - 可作为等价结构之间 transport 的一般引理。

- id: 定理 6.2
  kind: theorem
  status: 〔closed〕
  statement: 不存在单比特权重几何级数 `w_k=w₁Λ^{k-1}` 使其与 Zeckendorf 单比特取值成比例,因为 `F_{k+1}/F_k` 不是常数。
  depends_on: [定义 5.1]
  formalization_note: number-theoretic; 只需比较 `F₂/F₁`, `F₃/F₂`,或证明相邻比不恒定。
  formalizable_phase1: yes - 可用有理数或实数上的简单反证。

- id: 定理 6.3
  kind: theorem
  status: 〔closed〕
  statement: Fibonacci 递推的解空间二维,移位本征值为 `φ` 与 `ψ=-1/φ`,含 `F` 的最小移位不变权重空间是双面权重 `w_k=(φ^{k+1},ψ^{k+1})`,唯一至逐分量标度。
  depends_on: [定义 5.1, 定理 6.2]
  formalization_note: number-theoretic; 可用二阶线性递推、特征多项式 `x^2=x+1` 与 Binet 公式。
  formalizable_phase1: partial - mathlib 支持实二次根,但完整“最小扩张唯一”需设计线性代数接口。

- id: 定义 6.4
  kind: definition
  status: 〔定义〕
  statement: 定义双面长度 `λ₊,λ₋`,普通长度 `ℓ=(λ₊-λ₋)/√5`,以及单轴合法词生成函数 `W(x,y)`。
  depends_on: [定义 5.4, 定理 6.3]
  formalization_note: structural/inductive; `λ₊,λ₋` 可先作为有限和定义; `W` 若为无限和需 analytic layer。
  formalizable_phase1: partial - 有限位表长度可形式化,无限生成函数留到解析阶段。

- id: 定理 6.5
  kind: theorem
  status: 〔closed;窗口证书:相对误差 ≤ 4×10⁻¹⁶〕
  statement: 单轴生成函数满足重整化方程 `W(x,y)=W(φx,ψy)+exp(-xφ²+yψ²) W(φ²x,ψ²y)`。
  depends_on: [定义 6.4, 定理 6.3]
  formalization_note: structural/inductive; 作为合法词语言的首位分解可严格证明;窗口证书只验证数值实现。
  formalizable_phase1: partial - 可先证明有限深度/形式级数版本,解析收敛版本后置。

- id: 定理 6.6
  kind: theorem
  status: 〔closed;窗口证书:≤ 10⁻¹⁵〕
  statement: 对角线上 `W(x,x)=1/(1-exp(-√5 x))`,因此恢复 Euler 因子与 zeta;对角线不被重整化 `ℛ(x,y)=(φx,ψy)` 保持。
  depends_on: [定义 6.4, 定理 6.3, 定理 6.5]
  formalization_note: analytic/frontier; 对角坍缩可先做形式语言/几何级数证明,与 Euler 因子/zeta 的解析解释后置。
  formalizable_phase1: partial - 形式级数可证,完整解析读法不属于 phase 1。

- id: 定理 6.7
  kind: theorem
  status: 〔closed;窗口证书:窗口与密度吻合至 10⁻⁵〕
  statement: 膨胀面取值集 `B={Σu_k φ^{k+1}}` 是切割-投影模型集,共轭窗口为 `[-1/φ²,1/φ]`,窗口长为 `1`,密度为 `1/√5`,并满足 `B=φB ⊔ (φ²+φ²B)`。
  depends_on: [定理 5.3, 定理 6.3, 定义 6.4]
  formalization_note: number-theoretic; 代数恒等和窗口界可形式化,模型集密度需切割-投影/等分布理论。
  formalizable_phase1: partial - 先证明窗口包含和长度恒等,密度与模型集定理后置。

- id: 定理 6.8
  kind: theorem
  status: 〔closed;窗口证书〕
  statement: 收缩面读数 `λ₋` 对互素整数乘法可加,且其值由指数的 Zeckendorf 位形决定;不变轴对象写为 `Z_qc(s)=Σ e^{-sλ₋(n)} n^{-√5s}`。
  depends_on: [定理 4.4, 定理 5.3, 定义 6.4]
  formalization_note: number-theoretic; 互素可加性是素轴支撑不交时的有限和拆分; `Z_qc` 的级数性质后置。
  formalizable_phase1: yes - 可证明 `λ₋(mn)=λ₋(m)+λ₋(n)` for coprime;级数对象只登记定义。

- id: 定理 6.10
  kind: theorem
  status: 〔closed〕
  statement: 删除重整化算子 `ℛ` 后,双面提升、重整化函数方程、对角坍缩和模型集几何失去陈述资格,故 `ℛ` 是内核分量而非装饰。
  depends_on: [定理 6.3, 定理 6.5, 定理 6.6, 定理 6.7]
  formalization_note: analytic/frontier; 这是载荷/元理论断言,不适合直接作为普通 Lean theorem。
  formalizable_phase1: no - 可在文档层保留为设计说明,Lean 中只形式化其引用的具体定理。

- id: 命题 6.11
  kind: prop
  status: 〔closed·解析层;窗口证书〕
  statement: 在 `Re s>1` 上,Dirichlet 级数 `Σ λ₋(n)n^{-s}` 分解为 `ζ(s)·H(s)`,其中 `H` 是按素轴和收缩面读数 `β′` 写出的绝对收敛级数。
  depends_on: [定理 4.4, 定理 6.7, 定理 6.8]
  formalization_note: analytic/frontier; 需要 Dirichlet 级数绝对收敛、Euler 分层与重排定理。
  formalizable_phase1: no - phase 1 可只保留 statement-only 或定义级接口。

- id: 推论 6.11a
  kind: corollary
  status: 〔closed·解析层;窗口证书〕
  statement: 离对角不变量的平均论由对角层的 zeta 因子控制,所以 O-5 的开放方向只剩离对角到对角的回传。
  depends_on: [命题 6.11]
  formalization_note: analytic/frontier; 依赖解析平均估计与数值尾预算。
  formalizable_phase1: no - 只作为解析阶段目标。

- id: 命题 6.12
  kind: prop
  status: 〔closed;窗口证书〕
  statement: 不变轴对象有逐素轴 Euler 乘积 `Z_qc(s)=∏_p Σ_{v≥0}p^{-sβ(v)}`,且绝对收敛横标为 `1/φ²`。
  depends_on: [定理 4.4, 定理 6.7, 定义 6.4]
  formalization_note: analytic/frontier; 乘积和横标需要无限乘积和素数级数判别。
  formalizable_phase1: no - 可登记 `β` 与逐轴因子,不证横标。

- id: 命题 6.14
  kind: prop
  status: 〔closed·解析层;窗口证书〕
  statement: 在 `Re s>1/φ³` 上,`Z_qc(s)=ζ(φ²s)·G(s)`,且 `G` 在该域绝对收敛并在实轴为正。
  depends_on: [命题 6.12, 定理 6.7]
  formalization_note: analytic/frontier; 需要 Euler 因子首项剥离、绝对收敛域和正性证明。
  formalizable_phase1: no - 解析分解不进入 phase 1。

- id: 命题 6.16
  kind: prop
  status: 〔closed〕
  statement: 横标 `1/φ²` 由 Fibonacci Perron 根、模型集首元 `β(1)=φ²` 与 `1/min(B\{0})` 三步谱链决定。
  depends_on: [定理 6.1, 定理 6.3, 定理 6.7, 命题 6.12]
  formalization_note: analytic/frontier; 代数链可证,但横标本身依赖命题 6.12 的解析内容。
  formalizable_phase1: partial - 可证明 `β(1)=φ²` 与谱来源,横标结论后置。

- id: 命题 6.17
  kind: prop
  status: 〔closed;窗口证书〕
  statement: 二进制、Zeckendorf、Tribonacci 三种规范的谱指纹分别为 `1`, `φ²/√5`, `a·T*²`,三者互异。
  depends_on: [定理 6.2, 定理 6.3, 命题 6.16]
  formalization_note: numeric-window; Tribonacci 表示唯一性和常数收敛按文档只给有限窗口证书。
  formalizable_phase1: partial - 二进制/Zeckendorf 部分可证; Tribonacci 数值指纹应作为 computable certificate 或 statement-only。

- id: 命题 6.19
  kind: prop
  status: 〔closed·解析层;窗口证书〕
  statement: 在 `Re s>1/(2φ³)` 上,`Z_qc(s)=ζ(φ²s)ζ(φ³s)ζ(2φ²s)^{-1}exp(H₂(s))`,余项 `H₂` 绝对收敛,核心相消是 `φ²+φ³=φ⁴`。
  depends_on: [命题 6.14, 定理 6.7]
  formalization_note: analytic/frontier; 黄金相消是代数可证,ζ 级联与收敛域是解析层。
  formalizable_phase1: partial - 只形式化指数恒等式与有限阶形式级数相消。

- id: 命题 6.21
  kind: prop
  status: 〔closed;精确算术证书〕
  statement: Zeckendorf 归一化规则在双面账上内部规则零亏,底部规则产生带符号单位亏;解码看不见该纯隐藏亏空。
  depends_on: [定理 5.7, 定理 6.3, 定义 6.4]
  formalization_note: number-theoretic; 关键是 `φ` 的代数恒等式和 carry rule 的逐步守恒。
  formalizable_phase1: yes - 可先形式化有限 carry 规则和 `ℤ[φ]` 系数账。

- id: 定理 6.22
  kind: theorem
  status: 〔closed;窗口证书〕
  statement: 对 `c(v₁,v₂)=β(v₁)+β(v₂)-β(v₁+v₂)`,膨胀面亏空等于收缩面亏空,且 `c∈ℤ`,并等于底部进位事件的带符号计数。
  depends_on: [命题 6.21, 定理 6.3]
  formalization_note: number-theoretic; 用二次域共轭固定点 `ℚ∩ℤ[φ]=ℤ` 证明整性。
  formalizable_phase1: yes - 推荐用 `QuadraticField` 或显式 `a+bφ` 结构实现。

- id: 定理 6.23
  kind: theorem
  status: 〔closed;精确算术证书〕
  statement: 级联相消机制来自编码禁令词与其进位像的同指数赎回;Zeckendorf 的二阶相消和 Tribonacci 的三阶相消均是递推式的解析影。
  depends_on: [命题 6.19, 命题 6.21]
  formalization_note: number-theoretic; Zeckendorf 部分可由递推恒等式证明,Tribonacci 部分需要另建三阶规范。
  formalizable_phase1: partial - 先证 Fibonacci 禁词 `11 -> 100` 的相消。

- id: 推论 6.24
  kind: corollary
  status: 〔closed〕
  statement: 每阶级联最坏交叉项均为某禁令词,并由其进位像赎回,所以级联任意阶续行有结构保证。
  depends_on: [定理 6.23]
  formalization_note: structural/inductive; 全阶版本需要抽象合法词自动机和禁词赎回机制。
  formalizable_phase1: partial - 可先做低阶或 Fibonacci 自动机归纳骨架。

- id: 定理 6.25
  kind: theorem
  status: 〔closed〕
  statement: 对所有 `v₁,v₂≥1`,亏空 `c(v₁,v₂)` 只能取 `-1,0,+1`。
  depends_on: [定理 6.7, 定理 6.22]
  formalization_note: number-theoretic; 整性加共轭窗口长度界限即可。
  formalizable_phase1: yes - 在 6.7 的窗口包含与 6.22 整性完成后可短证。

- id: 推论 6.26
  kind: corollary
  status: 〔closed〕
  statement: 对所有 `m,n≥1`,收缩面读数偏离可加性的绝对值不超过 `log rad(gcd(m,n))`。
  depends_on: [定理 4.4, 定理 6.8, 定理 6.25]
  formalization_note: number-theoretic; 逐素轴累加 `|c_p|≤1` 并限制到公共素因子。
  formalizable_phase1: yes - 需先定义 `rad` 和有限素因子和。

- id: 命题 6.28
  kind: prop
  status: 〔(i) closed;(ii) closed·窗口,机制为数字层拟周期,完整证明经 Zeckendorf 里程计与黄金旋转之唯一遍历,属前沿〕
  statement: 亏空函数不含素数数据,因此对素数分类全盲;同时它不能由任何固定模同余读数判定,窗口实验给出黄金频率。
  depends_on: [定理 6.22, 定理 6.25]
  formalization_note: numeric-window; (i) 是定义展开, (ii) 的非同余与频率需黄金旋转唯一遍历或后续 Beatty 闭式。
  formalizable_phase1: partial - 先证素盲性;非同余和频率作为后续 theorem 或有限窗口证书。

- id: 命题 6.30
  kind: prop
  status: 〔closed·解析层;窗口证书〕
  statement: ζ 临界线在拟晶变量下拉回为 `s*=1/(2φ²)`,且该线也是字典分母 `ζ(2φ²s)` 的极点线;差 `2φ²-φ³=1` 是亏空硬币,结构零点斜率记录 `ζ(1/2)`。
  depends_on: [命题 6.19, 命题 6.21]
  formalization_note: analytic/frontier; 拉回线和代数差可证,零点斜率公式依赖 ζ 解析值与级联余项。
  formalizable_phase1: no - phase 1 只可登记代数恒等式 `2φ²-φ³=1`。

- id: 命题 6.32
  kind: prop
  status: 〔closed·解析层;窗口证书〕
  statement: ζ 反射经 `s_ζ=φ²s` 诱导拟晶反射 `J_qc(s)=1/φ²-s`;拉回线上分母安全,临界零点搬运到拉回线,并给出带内零点居线条件与 ζ 右半带无离线零点的等价。
  depends_on: [命题 6.19, 命题 6.30]
  formalization_note: analytic/frontier; 需要 ζ 函数方程、PNT 等价无零线、除子恒等式与极点相消分析。
  formalizable_phase1: no - 只保留 statement-only。

- id: 命题 6.34
  kind: prop
  status: 〔closed;窗口证书〕
  statement: 对 `Z_qc` 施用热迹中线普遍定理后,`Re s=1/(2φ²)` 同时是诱导反射不动线、拟晶酉性线、拟晶 ℓ² 边界与自共振线。
  depends_on: [命题 6.32, 定理 25.10]
  formalization_note: analytic/frontier; 依赖第二十五章普遍谱几何定理,超出 phase 1。
  formalizable_phase1: no - 等 25.10 形式化后再搬回。

- id: 定理 6.35
  kind: theorem
  status: 〔closed;窗口证书〕
  statement: 有限深度逐轴和 `W_K` 与权 `t_K` 满足递推 `W_{K+1}=W_K+t_{K+1}W_{K-1}`, `t_{K+1}=t_Kt_{K-1}`,因此由四维多项式映射轨道给出。
  depends_on: [定义 6.4, 定理 6.3]
  formalization_note: structural/inductive; 对最高位是否使用做有限词分解即可。
  formalizable_phase1: yes - 有限深度版本完全组合化。

- id: 定理 6.36
  kind: theorem
  status: 〔closed;窗口证书〕
  statement: 对数坐标 `u_K=-xφ^{K+1}+yψ^{K+1}` 上的二次型 `Q(a,b)=a²-ab-b²` 给出反不变量 `J_K=5xy(-1)^{K+1}`,其绝对值守恒。
  depends_on: [定理 6.3, 定理 6.35]
  formalization_note: number-theoretic; Binet 型二阶序列代入二次型直接计算。
  formalizable_phase1: yes - 可在多项式环或实数中证明。

- id: 定理 6.38
  kind: theorem
  status: 〔closed·逐阶;窗口证书〕
  statement: 模型集元素唯一写为 `aφ²+bφ³`,逐轴因子有双变量 Witt 分解,低总次指数表中 `e_{1,1}=0` 体现黄金相消。
  depends_on: [定理 6.7, 命题 6.19]
  formalization_note: numeric-window; Witt 分解形式可定义,但表格可信域由计算证书支撑。
  formalizable_phase1: partial - 只做形式幂级数定义和低阶可计算验证。

- id: 定理 6.40
  kind: theorem
  status: 〔closed;全阶,超越可信域〕
  statement: Witt 指数满足纯方向二阶终止、`a=1` 行三步截止、`b=1` 行无穷交替三条全阶封闭律。
  depends_on: [定理 6.38]
  formalization_note: structural/inductive; 可转化为一元形式幂级数除法和合法词枚举。
  formalizable_phase1: partial - 三条行律可分别形式化,完整 Witt 语义可后置。

- id: 命题 6.42
  kind: prop
  status: 〔closed·窗口;区间性与 Sturmian 分布之完整证明经黄金旋转,属前沿〕
  statement: Witt 格固定 `a` 的纤维容量只取 `{⌊φ³⌋,⌈φ³⌉}={4,5}`,固定 `b` 的对偶纤维容量只取 `{⌊φ²⌋,⌈φ²⌉}={2,3}`,支撑均为整区间。
  depends_on: [定理 6.7, 定理 6.38]
  formalization_note: numeric-window; 文中本条原标窗口/前沿,后续 6.48 给出闭合机制。
  formalizable_phase1: partial - 可先作为 6.48 的目标定理,不把窗口数据当证明。

- id: 定理 6.44
  kind: theorem
  status: 〔closed;精确算术证书:ℤ[φ] 至 2×10⁴、Beatty 至 2×10⁵;数学内容属经典(Beatty/Wythoff/切割-投影参数化),账本识别为新,依 25.9 先例标注〕
  statement: 位移解码 `S(v)` 满足 `β′(v)=S(v)-vφ`, `β(v)=S(v)-vψ`,且 `S(v)=⌊(v+1)φ⌋-1`。
  depends_on: [定理 6.7]
  formalization_note: number-theoretic; 经典 Beatty/Wythoff 公式,可用切割-投影窗口证明。
  formalizable_phase1: partial - 公式可作为重要目标,但 floor/irrational rotation 证明需谨慎。

- id: 推论 6.45
  kind: corollary
  status: 〔closed;复核证书:三形式互证 200²,旧证书表 {−1: 3296, 0: 33106, +1: 8748} 经 Beatty 公式逐字重现〕
  statement: 亏空可写为 `S(v₁)+S(v₂)-S(v₁+v₂)`,并由黄金相位和落入两个区间判定 `+1,-1,0`。
  depends_on: [定理 6.22, 定理 6.44]
  formalization_note: number-theoretic; 依赖 Beatty 闭式与 floor 小数部分运算。
  formalizable_phase1: partial - 在 6.44 后可证明;复核证书不代替证明。

- id: 定理 6.46
  kind: theorem
  status: 〔closed·二维等分布引注(核内化属 O-9 型余项);窗口证书:全矩形 10⁶ 对吻合至 10⁻⁴〕
  statement: 均匀取样下亏空分布频率为 `freq(+1)=1/(2φ²)`, `freq(-1)=1/(2φ⁴)`,期望为 `1/(2φ³)`。
  depends_on: [推论 6.45]
  formalization_note: analytic/frontier; 需要二维等分布/黄金旋转测度论,窗口证书仅作数值支持。
  formalizable_phase1: no - phase 1 可标 statement-only。

- id: 定理 6.47
  kind: theorem
  status: 〔closed;数值证书 n ≤ 2×10⁴〕
  statement: 令 `n_S=∏p p^{S(v_p(n))}`,则 `λ₊(n)=log n_S-ψ log n`, `λ₋(n)=log n_S-φ log n`,并可定义位移曲面 `𝔇(s,w)=Σ n_S^{-s}n^{-w}` 统一 `ζ` 与 `Z_qc` 两条截线。
  depends_on: [定理 4.4, 定理 6.44]
  formalization_note: number-theoretic; 两个 λ 恒等式是逐素轴有限和;曲面解析性质后置。
  formalizable_phase1: partial - 恒等式可证,Dirichlet 曲面仅定义。

- id: 定理 6.48
  kind: theorem
  status: 〔closed;复核修正一处〕
  statement: 纤维坐标满足 `a(v)=2S(v)-3v`, `b(v)=2v-S(v)`,固定 `a` 的纤维等价于 `2S(v)=3v+a` 加奇偶条件,容量 `{⌊φ³⌋,⌈φ³⌉}` 和区间支撑由此闭合。
  depends_on: [定理 6.42, 定理 6.44]
  formalization_note: number-theoretic; 使用 Beatty floor 公式和奇偶/区间判据。
  formalizable_phase1: partial - 适合作为 6.42 的证明目标,但 floor 区间技术较重。

- id: 定理 6.49
  kind: theorem
  status: 〔closed;精确 Fraction 延算至 v¹⁶〕
  statement: 前几行 Witt 行律满足显式公式,且 `g_a` 被 `g₀=1+v` 整除当且仅当纤维容量为偶;首个奇容量纤维产生无穷交替尾。
  depends_on: [定理 6.40, 命题 6.42, 定理 6.48]
  formalization_note: numeric-window; 部分行律为有限延算,一般机制依赖容量奇偶的全称证明。
  formalizable_phase1: partial - 可证明已给低行的形式幂级数恒等式,全称机制后置。

- id: 定理 6.50
  kind: theorem
  status: 〔closed;逐系数证书总次 ≤ 12〕
  statement: 二变量逐轴因子满足自函数方程 `F(u,v)=F(v,uv)+u·F(uv,uv²)`。
  depends_on: [定理 6.35, 定理 6.38]
  formalization_note: structural/inductive; 按是否用位 1 对合法词分解,总次证书只是实现检查。
  formalizable_phase1: yes - 可形式化为形式幂级数/语言等式。

- id: 定理 6.51
  kind: theorem
  status: 〔closed 于识别;前沿引注〕
  statement: 经幺模换元 `(P,Q)=(u²/v,v²/u³)`,逐轴因子成为 Hecke-Mahler 级数 `Σ P^{S(v)}Q^v`,且 Dirichlet 射线上第一变量因亏空硬币恒等式变成整变量。
  depends_on: [定理 6.44, 定理 6.50]
  formalization_note: analytic/frontier; 识别可代数化,Hecke-Mahler 经典理论只作外部接口。
  formalizable_phase1: partial - 可证明换元与指数等式,不接入超越性/延拓理论。

- id: 定理 6.53
  kind: theorem
  status: 〔closed;精确延算证书至行 7、v²²;有效域 a ≤ 7(原文 a ≤ 8 系勘误 E5,见定理 6.54)〕
  statement: 纤维多项式为区间指示 `g_a=v^{m(a)}(1-v^{cap(a)})/(1-v)`,容量奇偶决定 `r_a` 在 `v=-1` 是否有单极点,行尾振幅生成函数给出并裁决 BET-1。
  depends_on: [定理 6.48, 定理 6.49]
  formalization_note: numeric-window; 主要结论含有限行证书与行尾机制,需区分可证公式和延算裁决。
  formalizable_phase1: partial - 可形式化纤维多项式闭式,尾部裁决先作为 computable certificate。

- id: 定理 6.54
  kind: theorem
  status: 〔closed 于二阶;延算证书行 8 至 v²⁶;高阶为可检验预言〕
  statement: 行尾形态为 `(-1)^b` 乘多项式,次数由 `v=-1` 极点阶减一决定;二阶、三阶和层移行的多项式尾部由精确差分证书验证。
  depends_on: [定理 6.53]
  formalization_note: numeric-window; 二阶闭合有证书,高阶部分含预言性和延算验证。
  formalizable_phase1: partial - 建议只形式化极点阶到尾部次数的一般框架和已验证低阶。

- id: 定理 6.55
  kind: theorem
  status: 〔closed;双路证书 2×10⁻⁸〕
  statement: 位移曲面有 Euler 乘积 `𝔇(s,w)=∏_p f_φ(p^{-s},p^{-w})`,每个因子是完整二变量 Hecke-Mahler 级数。
  depends_on: [定理 4.4, 定理 6.47, 定理 6.51]
  formalization_note: analytic/frontier; 互素完全加性给形式乘积,解析收敛和双路数值证书后置。
  formalizable_phase1: partial - 可定义形式 Euler product,不证解析等式。

- id: 定理 6.57
  kind: theorem
  status: 〔(i)(iii) closed·逐阶;(ii) 前沿引注 + open 于严格边界;窗口证书〕
  statement: 逐阶 Witt 字典可把 `Z_qc` 亚纯推进到 `Re s>0` 任意紧段;虚轴为候选自然边界但严格边界仍开放;拉回线族全在安全区。
  depends_on: [定理 6.38, 定理 6.40, 定理 6.54, 定理 6.55]
  formalization_note: analytic/frontier; 自然边界和亚纯延拓是解析数论前沿,逐阶证书不是 universal proof。
  formalizable_phase1: no - 应标 statement-only/open frontier。

- id: 定理 6.58
  kind: theorem
  status: 〔closed;核查证书在案〕
  statement: 字典全部行函数在 `v=1` 可去且奇异点集为 `{−1}` 位于单位圆,所以行尾无指数增长而为多项式律。
  depends_on: [定理 6.49, 定理 6.54]
  formalization_note: numeric-window; 需把行函数作为有理函数族并证明奇点位置。
  formalizable_phase1: partial - 低行可计算验证,全族证明需更强行律。

- id: 定理 6.59
  kind: theorem
  status: 〔closed;五行验证〕
  statement: 行 `a` 的 `k` 阶极点部系数由 `((-1)^{k-1}/k)·[u^{a-4k}] F̄(u)^{-k}` 给出,并通过五个行例精确验证。
  depends_on: [定理 6.53, 定理 6.54]
  formalization_note: numeric-window; 公式骨架可形式化,当前支撑是五行验证。
  formalizable_phase1: partial - 作为 computable finite verification 比作为全称 theorem 更诚实。

## Part C - 骨架判断

### 1. phase 1 最该先形式化的 5-8 条定理

按依赖顺序:

1. 命题 2.4: 历史拼接结合与单位。它验证历史层的 inductive/list 编码是否正确,成本低且会被后续历史/证书复用。
2. 定理 3.2: 终止 + 局部合流推出唯一标准形。它是“单位性判据”的抽象骨架,可作为所有规范化论证的通用 lemma。
3. 定理 4.3-4.4: 素分解唯一与正自然数作为素数轴自由交换幺半群。mathlib 能大幅简化,且它支撑 PZG、Euler 乘积、地址原则。
4. 定理 5.3: Zeckendorf 唯一性。它是 PZG 位表唯一性的第二根支柱,需要真实证明,不能只留窗口核验。
5. 定理 5.5: PZG 解码双射。它把 FTA 与 Zeckendorf 逐轴唯一性合成,是核心编码定理。
6. 定理 5.6: 归一化唯一与乘法性。它给后续动态生成、PZG 加法和位表规范化提供接口。
7. 命题 6.21: 进位规则的双面账。它是第六章中最适合先形式化的非平凡代数内容,只需有限 carry 规则和 `φ` 恒等式。
8. 定理 6.22 与定理 6.25: 亏空整性与三值定理。二者把 `ℤ[φ]` 共轭、窗口长度和归一化亏空连接起来,内容非平凡且仍在代数/组合范围内。

### 2. 必须诚实标注为 numeric-window / open / statement-only 的条目

基础层中应避免直接作为 universal theorem 的条目:

- 6.17 的 Tribonacci 对照: 表示唯一性与谱常数在文档中依赖有限窗口证书,可做 executable check,不应直接当全称定理。
- 6.28(ii): 非同余性和黄金频率需要黄金旋转唯一遍历或 Beatty 闭式;窗口反例只支持有限范围。
- 6.42: 原状态含 `closed·窗口` 与“完整证明属前沿”,虽然 6.48 后续给出闭合路线;形式化时应以 6.48 为证明入口,不以 6.42 的窗口数据为证明。
- 6.46: 极限分布依赖二维等分布引注;窗口 `10^6` 对只可作为数值证书。
- 6.49, 6.53, 6.54, 6.58, 6.59: 多处行律、尾部振幅、极点谱系和层选择目前含有限延算或有限行验证;适合做 computable certificates,不宜统一声明全称闭合。
- 6.5, 6.6, 6.7, 6.8, 6.12, 6.14, 6.19, 6.30, 6.32, 6.34, 6.55, 6.57: 含无限生成函数、Euler product、ζ、解析延拓、PNT、零点搬运或自然边界等解析层内容。phase 1 可抽取有限/形式级数或代数恒等式,完整解析命题应 statement-only。
- 6.9 及 O-5 相关评注: 对角回传和 `Z_qc` 对 ζ 的独立解析控制仍为 open,不能以第六章字典本身冒充 RH 或零点控制。

### 3. 从素数轴 + Zeckendorf 双面 + 交换 σ 连接出的外部理论方向

1. 唯一分解、自由交换幺半群、Euler product: `ℕ₊` 的素数轴自由性连接到解析数论中 ζ 的 Euler 乘积与 von Mangoldt 单址读数。
2. Zeckendorf、Beatty/Wythoff、Sturmian/切割-投影模型集: Fibonacci 位表的唯一表示连接到准晶模型集、黄金旋转、Beatty 序列和窗口容量。
3. 二次域与共轭不变量: `ℚ(√5)` 的双面 `φ↔ψ` 给出亏空整性/迹型不变量,与第九章 `ℚ(i)` 的范数型二平方分类形成实/虚二次域对照。
4. Witt 分解、Hecke-Mahler 级数、Mahler/Hecke 理论: 第六章后半把逐轴合法词因子转成双变量形式幂级数、Witt 指数和 Hecke-Mahler 接口。
5. 反射/对角/自指逻辑: 最小交换 `σ` 连接不动点、对角反驳、闭合判定不可达与内化塔,为后续把语法自指和解析反射分层处理提供骨架。
