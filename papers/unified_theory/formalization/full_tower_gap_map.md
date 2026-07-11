# PZG-BEDC full tower formalization gap map

范围: `papers/unified_theory/PZG_BEDC_kernel_formal.md` 第〇章至第三十章,对照
`papers/unified_theory/lean4/UnifiedTheory/**/*.lean`。本图只记录形式化状态与施工边界,不把窗口证书、
前沿引注或语义说明当成 Lean 定理。

分类口径:

- `已证@M`: `UnifiedTheory.M` 中已有真实 Lean def/theorem,且不是 `True.intro` 假证。
- `thin-rewrap(纯包 mathlib X)`: mathlib 已有核心定理,项目只需包装到本文档语言。
- `待证-无条件`: 数学上可无条件形式化,项目尚未证明或只证明了较弱片段。
- `待证-conditional(h=...)`: 适合把外部重型定理、解析延拓、函数方程、显式公式、拓扑对偶等作为精确假设参数后证明本塔内蕴含。
- `开叶子(周边可证:...)`: 真开放问题或等价于 RH/独立解析控制/正性心脏的叶子。
- `纯叙事(...)`: 语义、规范、路线、对照、物理/哲学解释;可编码为 metadata,但无本层数学真值。

已确认的当前 Lean 覆盖面:

- `Foundation.Mark`: `Mark`, `Mark.sigma`, `sigma_involutive`, `sigma_ne_id`.
- `Foundation.History`: `MarkHist`, `append`, `append_assoc`, `Event`, `EventHist.generate`.
- `Foundation.Rewriting`: `Normal`, `Terminates`, `LocallyConfluent`, `newman_confluent`, `exists_unique_normal_form`.
- `Arithmetic.PrimeAxes`: `PrimeExp`, `PrimeExp.equivPNat`, `vp`, `vp_mul`.
- `Arithmetic.EuclidEscape`: `euclidEscape`, `exists_prime_not_mem`.
- `Arithmetic.Zeckendorf`: `AxisWord`, `AxisWord.decode/encode/equivNat`.
- `PZG.Carrier/Decode/Normalize`: `PZGTable`, `bit`, `equivPrimeExp`, `decode`, `encode`, `normAdd`, `decode_normAdd`, `vp_decode_normAdd`.
- `Golden.PhiInt/Lambda/Carry/Deficit/FiniteWords`: `PhiInt`, `betaPhi`, `lambdaPlus/lambdaMinus`, carry identities, `deficitPhi_integer`, Cassini.
- `Kernel.Components/LedgerStatus`: kernel slot aliases and four status constructors.
- `Reading.Fibers/TwoSquare`: pigeonhole fiber, square mod 4, prime two-square wrapper.
- `SelfCode.Diagonal`: Cantor-style no-classifier and no-decoder theorems.
- `Dynamics.CostArrow`: event-history cost arrow.

Mathlib probe notes:

- Confirmed: `Nat.factorizationEquiv`, `Nat.zeckendorfEquiv`, `Nat.Prime.sq_add_sq`,
  `Function.cantor_surjective`, `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`,
  `riemannZeta`, `completedRiemannZeta`, `completedRiemannZeta_one_sub`, `riemannZeta_one_sub`,
  `riemannZeta_eulerProduct`, `riemannZeta_eulerProduct_tprod`.
- Current import for zeta is `Mathlib.NumberTheory.LSeries.RiemannZeta` plus
  `Mathlib.NumberTheory.EulerProduct.DirichletLSeries`; `Mathlib.NumberTheory.ZetaFunction` is not present
  in this local mathlib tree.

## A. 逐章逐条表

### 第〇章 内核总对象

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 0.1 | 内核 `K` 是历史、生成、交换、素轴状态、PZG、读数、账本、自代码、相位、隐藏纤维、完成化、反射、性质与证书的总对象。 | 已证@Kernel.Components | 项目 alias; mathlib 只支撑各局部分量 | `UnifiedTheory/Kernel/Components.lean` | 当前只是 slot alias,若做成大 record 不应假装已证明全部载荷。 |

### 第一章 最小二分与交换

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 1.1 | 两个基本标记 `0,1` 作为最小二分。 | 已证@Foundation.Mark | `inductive` 无需 mathlib | `UnifiedTheory/Foundation/Mark.lean` | 不要把 `Bool` 当主接口,否则会把自然布尔语义带入。 |
| 定义 1.2 | 交换 `sigma` 互换两标记,且为非平凡对合。 | 已证@Foundation.Mark | `Function.Involutive` | `UnifiedTheory/Foundation/Mark.lean` | “唯一原始非平凡操作”是设计规范,Lean 只能证明给定 sigma 的性质。 |

### 第二章 历史、事件与生成公理

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 2.1 | 标记历史由空历史与带标记扩张有限生成,带长度和拼接。 | 已证@Foundation.History | `inductive`, recursion | `UnifiedTheory/Foundation/History.lean` | 文档拼接方向与 Lean `append` 方向须固定,否则后续等式会转置。 |
| 定义 2.2 | 生成事件是 `(src, op, arg, tag)` 四元组。 | 已证@Foundation.History | `structure` | `UnifiedTheory/Foundation/History.lean` | 当前 `Op Arg` 参数化,尚未固定 ISA;不能声称机器语义已给出。 |
| 定义 2.3 | 事件历史是事件有限序列,生成为接续事件。 | 已证@Foundation.History | `List.append`, length lemmas | `UnifiedTheory/Foundation/History.lean` | 当前证明的是 list 接续,不是第十五章执行语义。 |
| 公理 A1 | 生成归纳/时间性。 | 已证@Foundation.History | inductive/list induction | `UnifiedTheory/Foundation/History.lean` | Lean 中不应作为 axiom,应由 carrier 的 induction principle 得到。 |
| 公理 A2 | 每条历史有限。 | 已证@Foundation.History | `List`/inductive finite by construction | `UnifiedTheory/Foundation/History.lean` | 若后续引入流历史,必须另设 finite prefix 层,不可复用 A2。 |
| 命题 2.4 | 拼接结合,空历史为两侧单位。 | 已证@Foundation.History | recursion, `simp` | `UnifiedTheory/Foundation/History.lean` | 已证于 `MarkHist.append`;事件列表的 append 性质可另包。 |
| 命题 2.5 | 证书只引用有限多生成事件。 | 待证-无条件 | `List.length`, finite support | `UnifiedTheory/Kernel/Certificate.lean` | 需先定义 `Cert`;不能只凭“证书是历史”口头代替。 |

### 第三章 单位性判据

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 3.1 | 重写系统、标准形、终止、局部合流。 | 已证@Foundation.Rewriting | `Relation.ReflTransGen`, `WellFounded` | `UnifiedTheory/Foundation/Rewriting.lean` | 文档说“历史上关系”,当前 Lean 为任意类型泛型版,更强但需实例化。 |
| 定理 3.2 | 终止且局部合流推出唯一标准形。 | 已证@Foundation.Rewriting | 自建 Newman lemma over `ReflTransGen` | `UnifiedTheory/Foundation/Rewriting.lean` | 已证“存在唯一标准形”依 `Terminates`;若后续要算法 normalizer,还需可计算选择。 |
| 评注 3.3 | 单位性有 PZG、二平方范数、相位三种形态。 | 纯叙事(跨章索引) | 无 | `docs` 或 theorem index | 不要把三种“单位性”合成单个 Lean theorem,应分别引用 5.5/9.10/19.3。 |

### 第四章 素数轴与唯一分解

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 4.1 | 用单标记历史实现自然数、算术和素数谓词。 | thin-rewrap(纯包 mathlib `Nat`, `Nat.Prime`) | `Nat`, `Nat.Prime` | `UnifiedTheory/Arithmetic/NatFromHistory.lean` | mathlib 路线跳过“单标记历史实现”;若要忠实需给 `MarkHist ≃ Nat` 桥。 |
| 定理 4.2 | 每个 `n>1` 有有限素分解。 | thin-rewrap(纯包 mathlib `Nat.factorization`) | `Nat.factorization_prod_pow_eq_self`, `Nat.exists_prime_and_dvd` | `UnifiedTheory/Arithmetic/PrimeAxes.lean` | 当前项目未单列存在定理,只通过 `factorizationEquiv` 间接覆盖。 |
| 定理 4.3 | 素分解唯一至重排。 | thin-rewrap(纯包 mathlib `Nat.factorization_inj`) | `Nat.eq_of_factorization_eq`, prime factor list uniqueness | `UnifiedTheory/Arithmetic/PrimeAxes.lean` | 若需要文档的最小反例证明,mathlib wrapper 不展示该证明路线。 |
| 定理 4.4 | 正自然数乘法是素数轴上的自由交换幺半群,`vp` 乘法加性。 | 已证@Arithmetic.PrimeAxes | `Nat.factorizationEquiv`, `Nat.factorization_mul` | `UnifiedTheory/Arithmetic/PrimeAxes.lean` | `PrimeExp` 使用 `Finsupp`;要保持“自由交换幺半群”而非仅一个函数等式。 |
| 定理 4.5 | 有限素集的 Euclid 逃逸数有窗外素因子。 | 已证@Arithmetic.EuclidEscape | `Nat.exists_prime_and_dvd`, `Finset.prod` | `UnifiedTheory/Arithmetic/EuclidEscape.lean` | 现有定理给存在窗外素因子,但未显式包装 `E_S ≡ 1 mod p`。 |

### 第五章 Zeckendorf 尺度与 PZG 双射

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 5.1 | Fibonacci 尺度 `F_0=1,F_1=1,F_2=2,...`。 | 已证@Arithmetic.Zeckendorf | `Nat.fib`, `Nat.zeckendorfEquiv` | `UnifiedTheory/Arithmetic/Zeckendorf.lean` | mathlib Fibonacci index convention differs; document indices `k>=1` must be mapped explicitly. |
| 引理 5.2 | 隔位 Fibonacci 和为下一项减一。 | 待证-无条件 | `Nat.fib_add_two`, finite sums | `UnifiedTheory/Arithmetic/ZeckendorfSums.lean` | 不能由 `zeckendorfEquiv` 自动得到;需处理 parity/index shift。 |
| 定理 5.3 | Zeckendorf 表示存在唯一。 | 已证@Arithmetic.Zeckendorf | `Nat.zeckendorfEquiv` | `UnifiedTheory/Arithmetic/Zeckendorf.lean` | 当前使用 mathlib 的合法 index-list 表示,需在文档位词层给同构说明。 |
| 定义 5.4 | PZG 位表:每素轴 Zeckendorf 词,全局有限支撑,解码为素数幂积。 | 已证@PZG.Carrier/PZG.Decode | `Finsupp`, `Nat.factorizationEquiv` | `UnifiedTheory/PZG/Carrier.lean` | 必须保留逐轴 Zeckendorf carrier,不可直接塌成指数向量。 |
| 定理 5.5 | PZG 解码 `D : Z -> Nat+` 为双射。 | 已证@PZG.Decode | `Nat.factorizationEquiv`, `Nat.zeckendorfEquiv` | `UnifiedTheory/PZG/Decode.lean` | 证明是等价合成;若 paper 需要显式互逆定理,可再包 simp theorem。 |
| 定理 5.6 | 位表加法归一化后解码等于乘法。 | 已证@PZG.Normalize | `PNat.mul`, `Nat.factorization_mul` | `UnifiedTheory/PZG/Normalize.lean` | 当前 `normAdd` 定义为 decode 后乘积再 encode,不是 carry 算法。 |
| 定理 5.7 | Zeckendorf 后继进位链有限终止。 | 待证-无条件 | `Nat.zeckendorfEquiv`, well-founded recursion | `UnifiedTheory/PZG/CarryTerminate.lean` | 需定义具体 carry relation;不能用 `normAdd` canonical 定义代替进位过程。 |

### 第六章 规范载荷:自相似双面

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定理 6.1 | 忠实数字规范之间由解码合成给位词双射,解码性质规范不变。 | 待证-无条件 | equivalences, `Equiv` | `UnifiedTheory/Encoding/NormEquiv.lean` | 需定义“忠实规范”;否则 theorem 会弱成任意双射 tautology。 |
| 定理 6.2 | 一维几何权重不能按比例匹配 Fibonacci 取值。 | 待证-无条件 | `Nat.fib`, inequality/equality reasoning | `UnifiedTheory/Golden/SelfSimilar.lean` | 需量化 `w_k=w1*Lambda^(k-1)` 和“单比特成比例”的精确域。 |
| 定理 6.3 | Fibonacci 递推的最小精确自相似扩张是双面 `phi/psi`。 | 待证-无条件 | `Real.coe_fib_eq`, `Real.goldenRatio`, recurrence theory | `UnifiedTheory/Golden/SelfSimilar.lean` | “唯一至逐分量标度”需用二维解空间或矩阵本征向量精确定义。 |
| 定义 6.4 | 定义 `lambdaPlus/lambdaMinus` 与单轴生成函数 `W(x,y)`。 | 已证@Golden.Lambda(双面长度部分) / 待证-无条件(W) | `Finsupp.sum`, `Real.log`, summability | `UnifiedTheory/Golden/Lambda.lean`, `UnifiedTheory/Golden/WFunction.lean` | 现有 Lean 有 `lambdaPlus/lambdaMinus`,但没有无穷生成函数 `W`。 |
| 定理 6.5 | `W(x,y)` 满足 Fibonacci 首位分解的重整化方程。 | 待证-conditional(h=合法词级数绝对收敛与移位重排) | `Nat.zeckendorfEquiv`, summability/tprod | `UnifiedTheory/Golden/WFunction.lean` | 数值窗口证书不能替代无穷级数重排证明。 |
| 定理 6.6 | 对角坍缩 `W(x,x)=1/(1-exp(-sqrt 5*x))`。 | 待证-conditional(h=6.5 和对角收敛) | geometric series | `UnifiedTheory/Golden/WFunction.lean` | 需区分单轴词生成函数与全素数 Euler 因子。 |
| 定理 6.7 | `phi` 面取值集是切割-投影模型集,窗口长 1,密度 `1/sqrt 5`。 | 待证-无条件 | `Real.goldenRatio_irrational`, Beatty/Sturmian lemmas需自建 | `UnifiedTheory/Golden/ModelSet.lean` | mathlib 未必有模型集 API;需自建窗口/密度定义。 |
| 定理 6.8 | `lambdaMinus` 对互素乘法可加,定义 `Z_qc`。 | 待证-无条件(可加) / 待证-conditional(h=解析收敛)(`Z_qc`) | `Nat.Coprime`, factorization support | `UnifiedTheory/Golden/LambdaMultiplicative.lean`, `UnifiedTheory/Zeta/Quasicrystal.lean` | 当前 Lean 只有长度定义,未证明互素加性。 |
| 评注 6.9 | 双面对离对角载荷,对角回传为 O-5。 | 开叶子(周边可证:6.11-6.20 字典、6.35-6.59 组合簿记) | 无 | `UnifiedTheory/OpenProblems/O5.lean` | “载荷”是元性质,可做 dependency record,不能冒充零点控制。 |
| 定理 6.10 | 重整化算子 `R` 是承重内核分量。 | 纯叙事(载荷审计) | 无 | `UnifiedTheory/Kernel/LoadBearing.lean` | 可做元数据依赖图,不是普通数学命题。 |
| 命题 6.11 | `lambdaMinus` Dirichlet 级数在 `Re s>1` 分解为 `zeta(s)*H(s)`。 | 待证-conditional(h=绝对收敛和可加函数 Euler 分层) | `riemannZeta`, Euler product tools | `UnifiedTheory/Zeta/LambdaMinusDirichlet.lean` | 需精确定义 `beta'(v)` 与复级数;不能把窗口数值当 proof。 |
| 命题 6.12 | `Z_qc` 有逐轴乘积且绝对收敛横标 `1/phi^2`。 | 待证-conditional(h=模型集首元/收敛横标引理) | Euler product API, prime sum criteria需自建 | `UnifiedTheory/Zeta/Quasicrystal.lean` | “横标恰为”包含上下两方向;上界和发散证据都要形式化。 |
| 命题 6.14 | `Z_qc(s)=zeta(phi^2 s)*G(s)` 且 `G` 在右半平面绝对收敛。 | 待证-conditional(h=Euler 因子剥离与收敛估计) | `riemannZeta_eulerProduct`, tprod | `UnifiedTheory/Zeta/QuasicrystalFactor.lean` | 要处理复指数 `p^(-s*beta)` 的 branch/notation。 |
| 命题 6.16 | 横标 `1/phi^2` 来自编码谱链。 | 待证-无条件 | 6.3, 6.7, 6.12 | `UnifiedTheory/Golden/SpectralSignature.lean` | 依赖 6.12 完整横标,否则只能证明谱算术恒等式。 |
| 命题 6.17 | 二进制/Zeckendorf/Tribonacci 指纹互异。 | 待证-无条件(代数部分) / 待证-conditional(h=Tribonacci 表示唯一与 Pisot模型集) | algebraic numbers; likely self-built Tribonacci | `UnifiedTheory/Golden/EncodingFingerprints.lean` | 不要把有限扫描写成全称 Tribonacci theorem。 |
| 命题 6.19 | 二阶级联 `Z_qc=zeta(phi^2s) zeta(phi^3s) zeta(2phi^2s)^-1 exp H2`。 | 待证-conditional(h=Witt/Euler 乘积展开与尾收敛) | `riemannZeta_eulerProduct`, formal power series | `UnifiedTheory/Zeta/WittCascade.lean` | 解析域 `Re s>1/(2phi^3)` 是承重内容,不能只证明形式等式。 |
| 命题 6.21 | 进位规则在双面内部零亏,底部单位亏。 | 已证@Golden.Carry | `Real.goldenRatio_sq`, `Real.goldenConj_sq` | `UnifiedTheory/Golden/Carry.lean` | 现有 theorem 证明幂恒等式,还未绑定到具体 carry rewrite relation。 |
| 定理 6.22 | 亏空 `beta(v)+beta(w)-beta(v+w)` 是整数。 | 已证@Golden.Deficit | `PhiInt.fixed_conj_iff`, Zeckendorf decode | `UnifiedTheory/Golden/Deficit.lean` | 已证 `PhiInt` 整性,但未证明“底部进位事件计数”等解释项。 |
| 定理 6.23 | 禁令词、递推、解析相消三位一体。 | 待证-无条件(形式幂级数版) | polynomial/formal power series; Golden identities | `UnifiedTheory/Zeta/WittCascade.lean` | “每阶最坏交叉项”需要精确定义,否则语义过强。 |
| 推论 6.24 | 级联可续行至任意阶有结构保证。 | 待证-conditional(h=一般 Witt 级联机制) | formal power series/Witt transform需自建 | `UnifiedTheory/Zeta/WittCascade.lean` | 这是全阶机制,不能由低阶例子推出。 |
| 定理 6.25 | 亏空三值 `{-1,0,1}`。 | 待证-无条件 | 6.22 + Beatty/window bound; current `DeficitTrichotomy` only Prop | `UnifiedTheory/Golden/Deficit.lean` | 项目当前只有 statement Prop,未证明;不可标已证。 |
| 推论 6.26 | `lambdaMinus` 几乎加性,误差受 `log rad(gcd)` 控制。 | 待证-无条件 | 6.25, factorization support | `UnifiedTheory/Golden/LambdaAlmostAdditive.lean` | 依赖三值定理;互素精确可加不等于一般 almost additive。 |
| 命题 6.28 | 亏空素盲且非任何固定同余读数可判定。 | 待证-无条件 | Beatty/Sturmian equidistribution; modular counterexamples | `UnifiedTheory/Golden/DeficitBeatty.lean` | 非同余性要全 `m`,不能只列 `m<=60`。 |
| 命题 6.30 | 临界线拉回为 `1/(2phi^2)`,结构零点线携亏空硬币。 | 待证-conditional(h=6.19 字典与 zeta 在相关点性质) | `riemannZeta`, pole at 1需要 survey | `UnifiedTheory/Zeta/QuasicrystalPullback.lean` | “斜率记录 zeta(1/2)”需可微性和非零因子条件。 |
| 命题 6.32 | 拉回线定理:诱导反射、分母安全、零点搬运;右半带条件等价 RH。 | 待证-conditional(h=6.19除子恒等式 + PNT/ζ在Re=1无零) | `riemannZeta_one_sub`; PNT/zero-free line需 survey | `UnifiedTheory/Zeta/QuasicrystalPullback.lean` | 右半带等价 RH 是强结论,需严格处理极点相消与镜像。 |
| 命题 6.34 | 拟晶中线三重刻画由普遍热迹定理 25.10 得出。 | 待证-conditional(h=25.10 + Z_qc 横标) | Hilbert space/tsum | `UnifiedTheory/Zeta/QuasicrystalHilbert.lean` | 依赖 `Z_qc` 已定义为热迹且横标已证。 |
| 定理 6.35 | 逐轴有限和满足四维多项式迹映射递推。 | 待证-无条件 | finite words, recurrence | `UnifiedTheory/Golden/TraceMap.lean` | 有限递推易证;极限收敛是另一个解析命题。 |
| 定理 6.36 | Cassini-Fricke 反不变量 `J_K=5xy(-1)^(K+1)`。 | 已证@Golden.FiniteWords(有限 Cassini 心) / 待证-无条件(完整坐标) | `Nat.fib` Cassini, `Real.coe_fib_eq` | `UnifiedTheory/Golden/TraceMap.lean` | 当前只证明 Fibonacci Cassini,未证明 `u_K` 二次型公式。 |
| 定理 6.38 | Witt 级联指数表与唯一分解。 | 待证-无条件(形式簿记) / 待证-conditional(h=解析渐近) | formal power series, Möbius inversion | `UnifiedTheory/Zeta/WittCascade.lean` | “可信域表”不能替代全阶 theorem;表项可先 machine-check。 |
| 定理 6.40 | Witt 指数三条全阶封闭律。 | 待证-无条件 | formal power series, finite automata for legal words | `UnifiedTheory/Zeta/WittCascadeRows.lean` | 行 `b=1` 无穷交替需作为全称序列 theorem。 |
| 命题 6.42 | Witt 纤维容量 `{4,5}` 与 `{2,3}`。 | 待证-无条件 | Beatty/Sturmian lemmas需自建 | `UnifiedTheory/Golden/WittFibers.lean` | 当前窗口证书不能证明所有纤维区间性。 |
| 定理 6.44 | 位移读数 `S(v)=floor((v+1)phi)-1` 及 `beta` 闭式。 | 待证-无条件 | `Real.coe_fib_eq`, floor/Beatty | `UnifiedTheory/Golden/BeattyShift.lean` | floor 端点唯一性要用窗口开闭精确处理。 |
| 推论 6.45 | 亏空 Beatty 形式和相位判读。 | 待证-无条件 | 6.44, floor fractional part lemmas | `UnifiedTheory/Golden/DeficitBeatty.lean` | 需避免实数小数化;用 `fract` 或 `Int.floor` 定义。 |
| 定理 6.46 | 亏空极限分布三黄金频率。 | 待证-conditional(h=二维等分布/黄金旋转测度) | ergodic/equidistribution, likely self-built | `UnifiedTheory/Golden/DeficitDistribution.lean` | 数值频率不等于测度定理。 |
| 定理 6.47 | 位移曲面 `D(s,w)` 连接 `zeta` 与 `Z_qc`。 | 待证-conditional(h=6.44 + Dirichlet series convergence) | `riemannZeta`, summability | `UnifiedTheory/Zeta/ShiftSurface.lean` | 曲面等式需先固定复幂与收敛域。 |
| 定理 6.48 | 纤维坐标与容量定理闭合。 | 待证-无条件 | 6.44, floor inequalities | `UnifiedTheory/Golden/WittFibers.lean` | 起点公式边界是风险点,需要 exact floor proof。 |
| 定理 6.49 | 行律、容量奇偶与整除机制。 | 待证-无条件 | formal power series, 6.48 | `UnifiedTheory/Zeta/WittRows.lean` | `g_a/g_0` 的除法需在 Laurent/formal series 中定义。 |
| 定理 6.50 | 二变量自函数方程 `F(u,v)=F(v,uv)+uF(uv,uv^2)`。 | 待证-无条件 | legal word split, formal power series | `UnifiedTheory/Zeta/WittFunctionalEquation.lean` | 需定义 `F` 为形式级数或有收敛域的函数,不要混用。 |
| 定理 6.51 | Hecke-Mahler 识别。 | 待证-conditional(h=Beatty HM 级数理论接口) | no direct mathlib; floor-series self-built | `UnifiedTheory/Zeta/HeckeMahler.lean` | “识别”可证;“杠杆”不是零点控制。 |
| 定理 6.53 | 行尾振幅闭式。 | 待证-无条件 | formal power series, residue at `v=-1` algebra | `UnifiedTheory/Zeta/WittTail.lean` | 需把“尾部”定义为 eventually equal,并限定有效域。 |
| 定理 6.54 | 极点谱系和尾部多项式升维。 | 待证-无条件(有限阶) / 待证-conditional(h=一般阶组合定理) | formal power series | `UnifiedTheory/Zeta/WittTail.lean` | 高阶预言不能归入 theorem,除非给全阶 combinatorial proof。 |
| 定理 6.55 | 位移曲面有 Euler 乘积,因子为二变量 Hecke-Mahler 级数。 | 待证-conditional(h=互素完全加性 + 乘积收敛) | `EulerProduct.eulerProduct`, `riemannZeta_eulerProduct` | `UnifiedTheory/Zeta/ShiftSurfaceEuler.lean` | 逐轴级数收敛和全乘积收敛必须分开。 |
| 定理 6.57 | `Z_qc` 可逐阶亚纯推进至 `Re s>0` 紧段;虚轴为候选自然边界。 | 待证-conditional(h=全阶 Witt 字典和尾估计); 开叶子(周边可证:候选边界严格性) | zeta factors; natural boundary likely not mathlib | `UnifiedTheory/Zeta/QuasicrystalContinuation.lean` | 亚纯推进由 ζ 构造不是独立控制;边界严格性仍开放。 |
| 定理 6.58 | 编码层行函数奇异点在单位圆,行尾为多项式律。 | 待证-无条件 | rational functions/formal series | `UnifiedTheory/Zeta/WittSpectrum.lean` | 只适用于编码层,不得类推零点 RH。 |
| 定理 6.59 | 层选择公式读出极点部系数。 | 待证-无条件 | formal Laurent series, coefficient extraction | `UnifiedTheory/Zeta/WittTail.lean` | “五行验证”是 test;需全称公式 proof。 |
| 其余评注 6.13/6.15/6.18/6.20/6.27/6.29/6.31/6.33/6.37/6.39/6.41/6.43/6.52/6.56 | 对 O-5、级联、二次特权、手性、对手轮和 Hecke 文献关系的解释。 | 纯叙事(语义/路线/前沿引注;个别可拆成 theorem) | 依各自引用 | `UnifiedTheory/Notes/GoldenNarrative.lean` 或文档索引 | 若拆 theorem,必须回到对应编号定理,不要把解释性比喻形式化为数学事实。 |

### 第七章 本体同一性判据:总代码

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 7.1 | `Code(X)=PZG(data,rules,ledger)`。 | 待证-无条件 | structures, PZG encode | `UnifiedTheory/Kernel/Identity.lean` | 需先定义 `KernelObject` 的 data/rules/ledger 字段。 |
| 判据 7.2 | 内核同一性等价于总代码相等。 | 纯叙事(本体规范) | no | `UnifiedTheory/Kernel/Identity.lean` | 若作为 axiom 会强行决定对象相等;建议作为 setoid/quotient 定义。 |
| 定理 7.3 | 无隐形寄存器:不改变三分量即不改变对象。 | 待证-无条件(定义展开) | equality/setoid | `UnifiedTheory/Kernel/Identity.lean` | 只在 `=_K` 定义为 code equality 时为 rfl;外部对象相等则更强。 |
| 后果 7.4 | 账本层级和规则属于对象同一性。 | 纯叙事(规范后果) | no | `UnifiedTheory/Kernel/Identity.lean` | 可做 projections,但不应混入 Lean kernel equality。 |
| 评注 7.5 | 三性质经判据结为一体。 | 纯叙事(跨章组织) | no | theorem index | 需引用 3.2/5.5/17.3,不应建一个模糊总定理。 |

### 第八章 有限读数与窗口

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 8.1 | 有限读数只依赖有限多 PZG 坐标。 | 待证-无条件 | `Finset`, `Finsupp` | `UnifiedTheory/Reading/Window.lean` | 需形式化“只依赖有限坐标”的 extensional property。 |
| 定义 8.2 | 有限窗口 `W=(S,L,I,epsilon)`。 | 待证-无条件 | structures | `UnifiedTheory/Reading/Window.lean` | `I` 既可为时间窗口又可为复区域,建议用 sum type 或参数化。 |
| 定理 8.3 | 足够大的模读数分离不同自然数。 | 待证-无条件 | `Nat.mod_eq_of_lt`, inequalities | `UnifiedTheory/Reading/Window.lean` | 需明确 `R_M` 是 mod `M` 还是窗口上界读数。 |
| 定理 8.4 | 中国剩余:互素 `m,n` 时 `Z/(mn) ≃ Z/m × Z/n`。 | thin-rewrap(纯包 mathlib CRT) | `ZMod.chineseRemainder`, `Nat.Coprime` | `UnifiedTheory/Reading/CRT.lean` | 文档 proof 用自然数 divisibility; mathlib wrapper 应保持 ring equivalence 或 finite set version。 |
| 定理 8.5 | 有限读取必有纤维。 | 已证@Reading.Fibers | `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` | `UnifiedTheory/Reading/Fibers.lean` | 已证的是 finite carrier/classes 版本;需实例化到具体 `R_W`。 |
| 推论 8.6 | 有限读取只给投影,隐藏差异在 kernel 或账本。 | 待证-无条件(若定义 kernel) | 8.5 | `UnifiedTheory/Reading/Fibers.lean` | 需要定义 `ker R_W`;“或账本”是语义层。 |

### 第九章 读数分类范例:二轴范数

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 引理 9.1 | Euclid 引理 `p|ab -> p|a or p|b`。 | thin-rewrap(纯包 mathlib `Nat.Prime.dvd_mul`) | `Nat.Prime.dvd_mul` | `UnifiedTheory/Reading/TwoSquareFull.lean` | 项目未包装该引理;若要核内全链需显式 theorem。 |
| 命题 9.2 | `p∤a` 时 `a` 在 `ZMod p` 可逆。 | thin-rewrap(纯包 mathlib field/ZMod facts) | `ZMod`, `Fact p.Prime` | `UnifiedTheory/Reading/TwoSquareFull.lean` | 需处理 `p=0/1` 排除和 `ZMod p` field instance。 |
| 定理 9.3 | Fermat 小定理。 | thin-rewrap(纯包 mathlib Fermat) | `ZMod.pow_card_sub_one_eq_one`/Nat variants需 survey | `UnifiedTheory/Reading/TwoSquareFull.lean` | 文档证明是置换 proof;mathlib wrapper 路线不同。 |
| 定理 9.4 | Wilson 定理。 | thin-rewrap(纯包 mathlib Wilson) | `Nat.Prime.factorial_modEq_neg_one`需 survey | `UnifiedTheory/Reading/TwoSquareFull.lean` | 需确认具体 decl 名;不要凭记忆。 |
| 定理 9.5 | `-1` 平方剩余判据和 `m!` 见证。 | 待证-无条件 | Wilson, Fermat, `ZMod` | `UnifiedTheory/Reading/TwoSquareFull.lean` | 当前项目只包最终 prime two-square,未给见证 `m!`。 |
| 引理 9.6 | Thue 格点碰撞引理。 | 待证-无条件 | pigeonhole, integer bounds | `UnifiedTheory/Reading/Thue.lean` | 需精确处理 `floor sqrt p` 和非零差;这是构造性核心。 |
| 定理 9.7 | `p≡1 mod 4` 素数可写成两平方和。 | thin-rewrap(纯包 mathlib `Nat.Prime.sq_add_sq`) | `Nat.Prime.sq_add_sq` | `UnifiedTheory/Reading/TwoSquare.lean` | 现有 theorem 只给存在,不是文档的 Thue 构造 proof。 |
| 命题 9.8 | 平方模 4 只为 0/1,两平方和非 3 mod 4。 | 已证@Reading.TwoSquare | `Nat.pow_mod`, `omega` | `UnifiedTheory/Reading/TwoSquare.lean` | 已证包括 `not_three_of_sq_add_sq`,但只在 `Nat` 上。 |
| 引理 9.9 | `q≡3 mod4` 且 `q|a^2+b^2` 则 `q|a,b`,指数偶。 | 待证-无条件 | `ZMod`, 9.5, factorization | `UnifiedTheory/Reading/TwoSquareFull.lean` | 当前 final theorem 未证明一般指数偶必要性。 |
| 定理 9.10 | `n` 是两平方和 iff 每个 `3 mod 4` 素指数偶。 | thin-rewrap(纯包 mathlib `Mathlib.NumberTheory.SumTwoSquares`) / 已证@Reading.TwoSquare(素数特例) | `Nat.Prime.sq_add_sq`, sum-two-squares theorem需 survey | `UnifiedTheory/Reading/TwoSquareFull.lean` | 现有项目 theorem 是素数版,不是文档的一般 `n` 分类。 |
| 评注 9.11 | 读数-证书机器全链意义。 | 纯叙事(组织说明) | no | theorem index | 不应标为 formal theorem。 |

### 第十章 对偶完成:隐藏纤维与 solenoid

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 10.1 | 同余读数相容族 `Zhat`。 | 待证-无条件 | inverse limits or subtype of families | `UnifiedTheory/Completion/Profinite.lean` | 要固定 index category: divisibility poset vs all moduli with maps。 |
| 定理 10.2 | `Nat` 嵌入 `Zhat` 且在有限模窗口稠密。 | 待证-无条件 | CRT, lcm | `UnifiedTheory/Completion/Profinite.lean` | “稠密”需 topology;有限满足可先证明。 |
| 定理 10.3 | `Zhat ≅ prod_p Z_p`。 | 待证-conditional(h=mathlib p-adic/profinite API chosen) | `PadicInt`, profinite products需 survey | `UnifiedTheory/Completion/Profinite.lean` | `ZMod` inverse limit 与 `PadicInt` 产品的 topology 是主要风险。 |
| 评注 10.4 | 隐藏纤维为同余读数债,有正合列 `0->K∞->Σ∞->T->0`。 | 纯叙事(语义读法) | no | `UnifiedTheory/Completion/Solenoid.lean` | 正合列可形式化,但“债”是解释。 |
| 定理 10.5 | solenoid 元素模型,核为 `K∞`。 | 待证-conditional(h=chosen topology and solenoid construction) | topological groups, quotient/inverse limit | `UnifiedTheory/Completion/Solenoid.lean` | 元素层和拓扑层要分开;O-4 后续闭合不等于已在 Lean。 |
| 定理 10.6 | `Zhat` 连续特征群为 `Q/Z`。 | 待证-conditional(h=Pontryagin dual machinery or elementary topology lemmas) | topological groups; no direct full theorem confirmed | `UnifiedTheory/Completion/Duality.lean` | 需证明 T 无小子群、连续特征穿过有限层。 |
| 评注 10.7 | 读数-完成-读数闭环。 | 纯叙事(由10.3/10.6组织) | no | theorem index | 可在 10.6 完成后做 corollary,但不是独立内容。 |
| 定理 10.8 | 混合 solenoid `Σ∞` 连续特征群为 `Q`。 | 待证-conditional(h=10.6 + circle duality + quotient exactness) | `AddCircle`, topological group duality需 survey | `UnifiedTheory/Completion/SolenoidDuality.lean` | `T^∨≅Z` 与 quotient topology 是高风险。 |
| 评注 10.9 | 双闭环总结。 | 纯叙事(组织说明) | no | theorem index | 无需 Lean theorem。 |
| 定理 10.10 | 有限 Poisson 求和。 | 待证-无条件 | finite Fourier on `ZMod`, character orthogonality | `UnifiedTheory/Completion/FinitePoisson.lean` | 指数字符在 Lean 中需选择 `Complex.exp` 表示或抽象 character。 |
| 评注 10.11 | 有限 Poisson 到 theta/Poisson 的 O-9 过渡。 | 纯叙事(路线说明) | no | theorem index | 极限过渡是 23.9/23.10 的独立工作。 |

### 第十一章 residual 与四状态账本

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 11.1 | residual 是应满足性质而出现的非零差异。 | 待证-无条件 | structures | `UnifiedTheory/Kernel/Ledger.lean` | 需定义“应满足”上下文;否则 residual 只是一个 sigma type。 |
| 定义 11.2 | 账本条目含 source/detector/status/next。 | 已证@Kernel.LedgerStatus(状态词) / 待证-无条件(完整条目) | structures | `UnifiedTheory/Kernel/Ledger.lean` | 当前只有 status enum,没有条目结构。 |
| 定义 11.3 | 四状态 closed/open/tail/semantic 的语义。 | 已证@Kernel.LedgerStatus(枚举) / 纯叙事(语义) | inductive | `UnifiedTheory/Kernel/LedgerStatus.lean` | Lean 可枚举状态,但语义义务需另用 predicates。 |

### 第十二章 tail 演算

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 12.1 | 共尾窗口族覆盖每个有限窗口。 | 待证-无条件 | preorder/filter | `UnifiedTheory/Kernel/Tail.lean` | 建议用 filter/cofinal relation,避免 ad hoc list。 |
| 定义 12.2 | Tail certificate 包含共尾族、预算和控制条款。 | 待证-无条件 | structures, filters, inequalities | `UnifiedTheory/Kernel/Tail.lean` | `B(W)->0` 与单调可控是两种不同 certificate。 |
| 范例 12.3 | 素数轴、Euler 乘积尾、双面级数截断尾。 | 待证-无条件(素数轴已由4.5支撑) / 待证-conditional(h=级数尾估计) | `exists_prime_not_mem`, p-series estimates | `UnifiedTheory/Kernel/TailExamples.lean` | Euler 尾 `sum_{p>P}` 可用 `sum_{n>P}` 包,但双面尾需收敛假设。 |
| 定理 12.4 | tail 证书可加并给围合。 | 待证-无条件 | inequalities, filters | `UnifiedTheory/Kernel/Tail.lean` | 要清楚 residual 所在 normed group/order structure。 |
| 推论 12.5 | 数值验证 = 有限读数 + tail 预算。 | 待证-无条件(框架) | 12.4 | `UnifiedTheory/Kernel/Tail.lean` | 这是 certificate rule;应定义 checker 接受 pair。 |
| 定理 12.6 | 无穷是共尾有限窗口、tail 预算、分层闭合。 | 纯叙事(方法原则) | no | `UnifiedTheory/Kernel/Tail.lean` | 可形式化为 class of `TailClosed`,但等号式是口号。 |

### 第十三章 账本纪律与守恒

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 纪律公理 D | 每个非零 residual 要么被有限读数检出要么入账。 | 待证-conditional(h=LedgerDiscipline D) | no | `UnifiedTheory/Kernel/LedgerDiscipline.lean` | 这是义务条款,不应作为无条件事实。 |
| 定理 13.1 | 在 D 下空 open ledger 无本层可检 residual。 | 待证-conditional(h=LedgerDiscipline D) | elementary logic | `UnifiedTheory/Kernel/LedgerDiscipline.lean` | 需定义 `OpenLedger` 与 detectable residual。 |
| 定理 13.2 | 有限读数全称断言若假,反例历史第 0 层闭合。 | 待证-无条件 | decidable predicates, finite witness | `UnifiedTheory/Kernel/Falsifiability.lean` | “第 0 层”需形式化为 certificate type,否则只是可证伪性。 |

### 第十四章 自编码

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 14.1 | PZG-Gödel 码用前若干素数幂编码有限序列和事件。 | 待证-无条件 | `Nat.nth` primes需 survey, factorization | `UnifiedTheory/SelfCode/Godel.lean` | 需要 prime enumeration API;分隔码和 PZG 码是两套实现,要给互译。 |
| 定理 14.2 | 内核有限描述可编码为 PZG 对象。 | 待证-conditional(h=finite description of K and encoder correctness) | PZG decode, factorization | `UnifiedTheory/SelfCode/Godel.lean` | “内核有限描述”本身是元对象;需要固定 syntax datatype。 |
| 原则 14.3 | 自代码不是完整语义,真理判定升层。 | 纯叙事(语义边界;由17.4解释) | no | theorem index | 不应形式化为 `S(K) ≠ K` 除非二者同类型且语义明确。 |

### 第十五章 机器层:事件即指令

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 15.1 | ISA 含 Gen/Enc/Norm/Decode/Length/Phase/Read/Ledger/Renorm/Complete/Reflect/Certify。 | 待证-无条件 | finite inductive | `UnifiedTheory/SelfCode/ISA.lean` | 当前 `Event` 的 `Op` 参数尚未实例化为 ISA。 |
| 定义 15.2 | 替换算子 `Sub` 把码作为参数接入自身描述。 | 待证-无条件 | syntax trees, encoders | `UnifiedTheory/SelfCode/Substitution.lean` | 需 de Bruijn/quote 机制;字符串拼接不忠实。 |
| 机器公设 U | 输入码运行总终止于本文所用变换;一般求值总性仍 O-1。 | 待证-conditional(h=EvalTerminates fragment) | computability theory | `UnifiedTheory/SelfCode/Machine.lean` | 不要声明全程序总性;应只给直线片段 theorem 和一般片段 hypothesis。 |

### 第十六章 不动点与对角三定理

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定理 16.1 | 对核内可计算码变换存在 Kleene 不动点。 | 待证-conditional(h=U + substitution/evaluator correctness) | recursion theorem not in current project | `UnifiedTheory/SelfCode/FixedPoint.lean` | 现有 `SelfCode.Diagonal` 只证明 Cantor,不是 Kleene fixed point。 |
| 定理 16.2 | 同层闭合判定器不存在。 | 已证@SelfCode.Diagonal(抽象 Cantor 影子) / 待证-conditional(h=U for exact kernel closure) | `Function.cantor_surjective` | `UnifiedTheory/SelfCode/ClosureDiagonal.lean` | Cantor no-classifier 比文档 closure predicate 抽象;要桥接 `C` 和 ledger closure。 |
| 定理 16.3 | 性质层/流层/总求值器不可穷举。 | 已证@SelfCode.Diagonal(性质层影子) / 待证-conditional(h=evaluator model) | Cantor diagonal | `UnifiedTheory/SelfCode/Diagonal.lean` | 流空间和程序轨道部分尚未形式化。 |
| 定理 16.4 | `sigma` 是对角引擎的承重分量。 | 纯叙事(载荷审计) | `Mark.sigma` | `UnifiedTheory/Kernel/LoadBearing.lean` | 可做 dependency statement,但不是普通 theorem。 |

### 第十七章 性质提升公理与内化塔

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 17.1 | 性质对象 `PObj(P)` 含历史、PZG、读数、账本、自代码、更新、证书。 | 待证-无条件 | structures | `UnifiedTheory/Tower/PropertyObject.lean` | 需要区分 object-level property 与 Lean `Prop`。 |
| 公理 17.2 | 使用的性质必须对象化进入内核。 | 待证-conditional(h=PropertyLift for chosen class) | no | `UnifiedTheory/Tower/PropertyObject.lean` | 一般性质提升不可无条件声称,否则与 16.3 冲突。 |
| 定理 17.3 | 被使用性质的典范构造与有限生成概念三性质继承。 | 待证-conditional(h=U for self-code) / 待证-无条件(有限生成继承框架) | induction over syntax | `UnifiedTheory/Tower/FiniteGenerated.lean` | 将一般性质和有限生成类分开,否则过强。 |
| 定理 17.4 | 内化塔良定、无封顶、semantic 即层移接口、闭合谓词需层级。 | 待证-conditional(h=U + formal tower syntax) | Cantor/Godel style, inductive tower | `UnifiedTheory/Tower/Internalization.lean` | “每层存在不可判闭合断言”需精确证明或作为 Gödel-style hypothesis。 |
| 定义 17.5 | 层移算子把 semantic 账移为上一层对象的 open 义务。 | 待证-无条件 | structures/functions | `UnifiedTheory/Tower/Shift.lean` | 需定义 source/detector 编码追溯。 |
| 命题 17.6 | 层移与提升构造相容。 | 待证-conditional(h=17.3 construction) | record extensionality | `UnifiedTheory/Tower/Shift.lean` | “逐案展开属 O-3”要作为 separate cases。 |
| 定理 17.8 | `Con(T_alpha)` 可反驳不可证实,为塔燃料。 | 待证-conditional(h=Gödel/Tarski/closure diagonal formalization) | mathematical logic not in current mathlib scope | `UnifiedTheory/Tower/ConsistencyFuel.lean` | 真正不可证实不应由 Cantor 直接替代;需 proof system semantics。 |
| 范例 17.9 | `Con` 的层移逐案流程。 | 待证-conditional(h=17.8 + Shift) | tower definitions | `UnifiedTheory/Tower/Examples.lean` | “公理化下一层”是 construction choice,需 explicit extension operation。 |
| 评注 17.10 | 塔永不塌缩与四状态必要性。 | 纯叙事(总结) | no | theorem index | 不需 Lean。 |

### 第十八章 状态、素数地址与时间之矢

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 18.1 | 状态 `K_t=(a,z,theta,r,ledger)`。 | 待证-无条件 | structures | `UnifiedTheory/Dynamics/State.lean` | 当前只用 EventHist 成本,未定义完整 state。 |
| 定义 18.2 | 合法生成事件为有限支撑素轴向量,更新 `a+u` 与 PZG 归一化。 | 待证-无条件 | `Finsupp`, `PZGTable.normAdd` | `UnifiedTheory/Dynamics/State.lean` | 要连接 `PrimeExp` 加法与 `PZGTable.normAdd`。 |
| 推论 | 乘法是指数生成的解码影子,非空状态长度正。 | 待证-无条件 | `vp_mul`, `Real.log_pos` for primes | `UnifiedTheory/Dynamics/ExponentState.lean` | `log p >0` 需 `p>=2`;支撑只含 prime。 |
| 定理 18.3 | 每步合法运动有有限非空素数地址。 | 待证-无条件 | `Finsupp.support` | `UnifiedTheory/Dynamics/Address.lean` | “非合法变化入账”依纪律 D,应条件化。 |
| 定理 18.4 | 合法轨迹逐步唯一编码,同状态 iff 同 PZG 码和同账本。 | 待证-conditional(h=identity criterion 7.2 + state definitions) | PZG decode | `UnifiedTheory/Dynamics/State.lean` | 如果 state 还含 `theta/r`,需证明它们由 code+ledger 决定或调整 statement。 |
| 定理 18.5 | 事件列唯一决定状态轨道。 | 已证@Dynamics.CostArrow(生成历史单调影子) / 待证-无条件(完整轨道) | list recursion | `UnifiedTheory/Dynamics/Trajectory.lean` | 当前只证明 event append 长度增长和不等,不是 state transition determinism。 |
| 定义 18.6 | 长度读数 `L(a)=sum a_p log p`。 | 待证-无条件 | `Finsupp.sum`, `Real.log` | `UnifiedTheory/Dynamics/Length.lean` | 对 `PrimeExp` 和 groupified `Z` state 要分两个函数。 |
| 定理 18.7 | 正生成使 `L` 严格增加。 | 已证@Dynamics.CostArrow(列表成本版) / 待证-无条件(素轴长度版) | `Real.log_pos`, finite sum positivity | `UnifiedTheory/Dynamics/Length.lean` | 不要把事件数量成本定理等同于 log 长度定理。 |
| 定理 18.8 | 地址三分并由二平方分类读取。 | 待证-无条件 | `Nat.mod`, two-square classification | `UnifiedTheory/Dynamics/AddressClassification.lean` | 项目目前只有素数 two-square wrapper,需补一般分类或 prime 分类足够版。 |
| 定义 18.9 | 群化账本和逆事件。 | 待证-无条件 | `ℕ→₀ℤ`, free abelian groups | `UnifiedTheory/Dynamics/Groupified.lean` | 负事件 ledger 引用对象需单独定义。 |
| 定理 18.10 | 群化状态同构于正有理乘法群。 | 待证-无条件 | `Rat`, factorization of rationals需 survey | `UnifiedTheory/Dynamics/Groupified.lean` | 自然数 factorization 不直接给 `Q+`;需自建 finite integer exponent product。 |
| 定理 18.11 | 流水成本随非零事件严格增加。 | 已证@Dynamics.CostArrow(事件数量版) / 待证-无条件(log variation版) | absolute values, finite support | `UnifiedTheory/Dynamics/CostArrow.lean` | 当前 theorem 是 list length,需要 log cost version 才忠实。 |
| 推论 18.12 | 不可逆性移到账本流水层。 | 已证@Dynamics.CostArrow(append_ne) / 待证-无条件(账本层) | 18.11 | `UnifiedTheory/Dynamics/CostArrow.lean` | 需定义冲销不删除原条目。 |

### 第十九章 相位与酉性线

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 19.1 | 相位读数 `Phi_s(a)=exp(-sL(a))`,纯相位模长 1。 | 待证-无条件 | `Complex.exp`, `Complex.normSq`, `Real.exp` | `UnifiedTheory/Dynamics/Phase.lean` | 要区分 real length 与 complex parameter。 |
| 定义 19.2 | 半密度归一化和缩放账 `Lambda_s(a)=delta L(a)`。 | 待证-无条件 | structures/functions | `UnifiedTheory/Dynamics/Phase.lean` | `delta=Re s-1/2` 应用 `Complex.re`。 |
| 定理 19.3 | `Re s=1/2` iff 归一化后逐项模 1 iff 缩放账为 0。 | 待证-无条件 | `Complex.normSq_exp`, `Real.exp_eq_one_iff` | `UnifiedTheory/Dynamics/UnitarityLine.lean` | 反向取 `a=e_2` 需定义非空 prime axis state。 |
| 推论 19.4 | 离线缩放账非零且沿 `me_2` 无界。 | 待证-无条件 | real inequalities | `UnifiedTheory/Dynamics/UnitarityLine.lean` | “同号”依 `L(a)>0`;空账本例外必须排除。 |
| 定理 19.5 | 反射不动线和酉性线重合。 | 待证-无条件 | complex arithmetic | `UnifiedTheory/Dynamics/UnitarityLine.lean` | 需定义 `Theta/J`;不要依赖 zeta 函数。 |
| 定理 19.6 | 相位分裂为双面参数读数。 | 待证-无条件(定义桥) | `lambdaPlus/lambdaMinus` | `UnifiedTheory/Dynamics/Phase.lean` | “时频对偶扩充”是解释;Lean 证明应是 projection identities。 |

### 第二十章 可见-隐藏动力学

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 20.1 | 可见轨迹是到 solenoid 的路径,投影到 circle。 | 待证-conditional(h=solenoid model) | topological spaces | `UnifiedTheory/Dynamics/SolenoidFlow.lean` | 需先固定 `Σ∞` topology。 |
| 规格 20.2 | 可见合法轨迹为 C1 或分段 C1。 | 待证-无条件(谓词定义) / 纯叙事(规格) | `ContDiff`, interval API | `UnifiedTheory/Dynamics/SmoothLegality.lean` | “不可导点入账”需 ledger discipline。 |
| 定理 20.3 | 连通实区间到 `K∞` 的连续映射常值。 | 待证-conditional(h=K∞ product topology and discrete finite projections) | connectedness, discrete topology | `UnifiedTheory/Dynamics/HiddenRigidity.lean` | `Z_p` 本身不离散;证明应经 finite quotient projections,不是直接 `Z_p` discrete。 |
| 推论 20.4 | 隐藏变化只能离散跳转或搭载整体相位路径。 | 待证-conditional(h=20.3 + solenoid exact sequence) | topological group | `UnifiedTheory/Dynamics/HiddenRigidity.lean` | “非法入账”依 D。 |
| 定义 20.5 | 喉部 `Th(theta)=pi^-1(theta)`。 | 待证-conditional(h=solenoid projection) | preimage | `UnifiedTheory/Dynamics/Throat.lean` | 若 `pi` quotient map, fiber equality to translate of kernel needs group action proof。 |
| 定理 20.6 | 局部提升差给 `K∞` cocycle,满足乘法 cocycle。 | 待证-conditional(h=principal bundle/local sections) | group algebra | `UnifiedTheory/Dynamics/Cocycle.lean` | 若没有 open cover/local section API,先做 abstract cocycle lemma。 |
| 推论 20.7 | 隐藏跳转必须满足 cocycle 一致性。 | 待证-conditional(h=20.6 + ledger rule) | 20.6 | `UnifiedTheory/Dynamics/Cocycle.lean` | 合法运动谓词需定义。 |
| 定义 20.8 | 动力窗口 `K_S=prod_{p in S} Z_p`,有限窗口有 tail。 | 待证-conditional(h=p-adic product API) | finite products | `UnifiedTheory/Dynamics/Window.lean` | `Z_p` finite window若取完整 p-adic 仍无限;读数深度也要纳入。 |
| 评注 20.9 | 动力学约束总表。 | 纯叙事(索引表) | no | docs | 不需 Lean。 |
| 定理 20.10 | solenoid 连续路径分解为实提升加常值隐藏偏移。 | 待证-conditional(h=path lifting for circle and inverse limit solenoid) | `AddCircle`, covering/lift lemmas | `UnifiedTheory/Dynamics/SolenoidFlow.lean` | 这是高拓扑定理,不要只证明 finite coordinate statement。 |
| 推论 20.11 | 路径分支为流线,隐藏迁移只能离散跳转。 | 待证-conditional(h=20.10) | quotient by integer action | `UnifiedTheory/Dynamics/SolenoidFlow.lean` | 分支集 `K∞/Z` 需 quotient rigor。 |
| 定理 20.12 | `K∞` 序列紧。 | 待证-conditional(h=countable product of finite quotients / compactness) | compactness, diagonal extraction | `UnifiedTheory/Completion/Compactness.lean` | `K∞` as product of `Z_p` compact; sequence compact in non-metrizable product needs care; countable index helps。 |
| 评注 20.13 | 对角反驳和对角紧致同源。 | 纯叙事(类比) | no | docs | 不形式化。 |
| 命题 20.14 | 任一流线整数时移遍历任意有限隐藏读数类。 | 待证-conditional(h=CRT + solenoid flow model) | CRT | `UnifiedTheory/Dynamics/SolenoidFlow.lean` | “遍历全部读数类”是 finite exact surjectivity,不是 topological equidistribution。 |
| 评注 20.15 | 平行时间线严格形态。 | 纯叙事(由20.10/20.14组织) | no | docs | 不形式化。 |

### 第二十一章 从最小核到传统对象

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 路线 21.1 | 从 `N -> Z -> Q -> R -> C` 以群完成、局部化、完备化、代数商生成传统对象。 | thin-rewrap(纯包 mathlib numeric tower) | `Int`, `Rat`, `Real`, `Complex`, quotient/localization APIs | `UnifiedTheory/Numbers/Tower.lean` | 如果目标是“从最小核生成”,mathlib wrapper 只证明存在同构,不重演构造。 |
| 评注 21.2 | `a^2+b^2` 的四重身份。 | 纯叙事(跨章组织) | no | theorem index | 可引用 9.10/21.1/18.8。 |
| 定义 21.3 | 核内导数以模数形式定义,给 C1 谓词。 | 待证-无条件 | analysis derivatives, constructive modulus structures | `UnifiedTheory/Numbers/Derivative.lean` | 若用 mathlib `HasDerivAt`,会弱化“带模数”的构造性内容。 |

### 第二十二章 热迹与 Euler 判据

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 22.1 | `Z_K(s)=sum_{z in Z} exp(-s ell(z)) = zeta(s)` for `Re s>1`。 | 待证-无条件(定义与PZG桥) / thin-rewrap(zeta) | `riemannZeta`, `tsum`, PZG decode | `UnifiedTheory/Zeta/HeatTrace.lean` | 需证明 PZG `ell=log decode`;当前 `ell` 尚未定义为 log。 |
| 定理 22.2 | 形式热迹有 Euler 因子 iff monoid free on atoms; Hilbert monoid反例。 | 待证-无条件(抽象判据) / 待证-conditional(h=Hilbert monoid finite count proof) | `EulerProduct.eulerProduct`; monoid algebra | `UnifiedTheory/Zeta/EulerCriterion.lean` | “ iff ” 很强,需精确定义自由原子分解与形式热迹。 |
| 定理 22.3 | `zeta(s)=prod_p (1-p^-s)^-1` for `Re s>1`。 | thin-rewrap(纯包 mathlib `riemannZeta_eulerProduct`) | `riemannZeta_eulerProduct`, `riemannZeta_eulerProduct_tprod` | `UnifiedTheory/Zeta/EulerProduct.lean` | 注意本地 zeta import path 是 `LSeries.RiemannZeta` + `EulerProduct.DirichletLSeries`。 |
| 定义 22.4 | 带标签 zeta 向量 `Z_vec(s)=sum_a exp(-sL(a))|a>` 与忘标签投影。 | 待证-无条件 | `HilbertSpace`, `lp`, formal functions | `UnifiedTheory/Zeta/TaggedVector.lean` | “逐坐标无收敛义务”和 `l2` 子空间要分两个 carriers。 |
| 定理 22.5 | 带标签向量永不为零,空账本系数为 1。 | 待证-无条件 | function extensionality | `UnifiedTheory/Zeta/TaggedVector.lean` | 只对 formal product carrier 无条件;若在 `l2`,需 `Re s>1/2`。 |
| 推论 22.6 | 零点是忘标签投影相消,不是本体向量消失。 | 待证-conditional(h=22.5 + projection definition + analytic continuation) | `riemannZeta` | `UnifiedTheory/Zeta/TaggedVector.lean` | 投影在临界带不由收敛求和定义,需延拓桥。 |

### 第二十三章 完成化契约与反射

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 契约 23.1 | 保守解析延拓需保持编码/账本/无自由缩放寄存器/残差入账。 | 纯叙事(规格) | no | `UnifiedTheory/Zeta/Contract.lean` | 可编码为 structure of obligations,不是 theorem。 |
| 定义 23.2 | 缩放寄存器是逐项依赖账本且未入账的因子。 | 待证-无条件 | structures/functions | `UnifiedTheory/Zeta/Contract.lean` | “未入账”需 ledger state predicate。 |
| 定理 23.3 | 解析延拓唯一。 | thin-rewrap(纯包 mathlib analytic identity theorem) / 待证-无条件(若重建) | identity theorem for analytic functions需 survey | `UnifiedTheory/Analysis/AnalyticContinuation.lean` | 文档给核内重建 proof;mathlib wrapper 不保留构造性尾控。 |
| 定理 23.4 | C3a:同一 germ 与同一总代码不能添加缩放寄存器。 | 待证-conditional(h=23.3 + 7.2 identity criterion) | 23.3 | `UnifiedTheory/Zeta/Contract.lean` | “不能添加”是 no-existence theorem over extensions,需定义 extension object。 |
| 定义 23.5 | 完成读数 `Lambda_K` 与 `xi_K`。 | 已由 mathlib 可 thin-rewrap / 待建项目 wrapper | `completedRiemannZeta`, `completedRiemannZeta₀` | `UnifiedTheory/Zeta/Completed.lean` | mathlib `completedRiemannZeta` 与文档 `xi=1/2 s(s-1)Lambda` 要分清。 |
| 定理 23.6 | 完成 zeta 满足函数方程。 | thin-rewrap(纯包 mathlib `completedRiemannZeta_one_sub`) | `completedRiemannZeta_one_sub`, `completedRiemannZeta₀_one_sub` | `UnifiedTheory/Zeta/Completed.lean` | 若要整函数 `xi` 版本,还要证明极点消除和 scalar factors。 |
| 定理 23.7 | 完成因子是全局 ledger,不是逐项缩放寄存器。 | 待证-无条件(定义展开) | `Complex.Gamma`, pi powers | `UnifiedTheory/Zeta/Contract.lean` | 需在 23.2 下证明 arch factor 不依赖 `a`。 |
| 命题 23.8 | `J(s)=1-conj(s)` 不动线为 `Re s=1/2`。 | 待证-无条件 | complex arithmetic | `UnifiedTheory/Zeta/Reflection.lean` | 与函数方程无关,是纯几何。 |
| 定理 23.9 | theta 方程 `theta(t)=t^-1/2 theta(1/t)`。 | 待证-conditional(h=Poisson summation/Gaussian integral) | theta/Poisson APIs需 survey | `UnifiedTheory/Zeta/Theta.lean` | mathlib zeta continuation可绕过 theta proof;若忠实重建需积分细节。 |
| 定理 23.10 | Mellin 传递给完成表示、延拓、极点和函数方程。 | thin-rewrap(纯包 mathlib completed zeta) / 待证-conditional(h=23.9 + Mellin integral machinery) | `completedRiemannZeta_eq`, `completedRiemannZeta_one_sub` | `UnifiedTheory/Zeta/Mellin.lean` | 项目若用 mathlib,不要声称已经核内重建 theta/Mellin。 |
| 推论 23.11 | O-9 解析机器四石闭合。 | 待证-conditional(h=23.3/10.10/23.9/23.10 in project) | above | `UnifiedTheory/Zeta/Completed.lean` | 当前 Lean 项目没有这些四石,不可标已证。 |

### 第二十四章 零点账本

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 24.1 | 投影零点是忘标签投影为零,有限零点读取是窗口事件。 | 待证-无条件(定义) | `riemannZeta`, completed zeta | `UnifiedTheory/Zeta/ZeroLedger.lean` | “延拓意义下投影”需用 completed/riemannZeta 函数,非收敛和。 |
| 定义 24.2 | 逐项缩放账 `delta log n`。 | 待证-无条件 | 19.2 | `UnifiedTheory/Zeta/LocalScale.lean` | 和 19.2 重复,建议复用定义。 |
| 定理 24.3 | 离线本地缩放账不可由旋转或全局因子清除。 | 待证-无条件 | real/complex norm algebra | `UnifiedTheory/Zeta/LocalScale.lean` | “任何 a-无关因子”需量化为 complex scalar `g`。 |
| 定理 24.4 | 镜像反转缩放账: `Lambda_{J(s)}=-Lambda_s`。 | 待证-无条件 | complex arithmetic | `UnifiedTheory/Zeta/Reflection.lean` | 空账本例外不影响等式。 |
| 定理 24.5 | 实系数+反射给零点四元组和跨位置缩放账配对;仪器有离线例。 | 待证-conditional(h=analytic function real-symmetry and functional equation) / 纯叙事(仪器窗口) | complex conjugation, zeros | `UnifiedTheory/Zeta/ReflectionZeros.lean` | 非乘性 Dirichlet 型仪器若只数值存在,不能作 Lean theorem 除非给精确定义和 proof。 |
| 推论 24.6 | 本地闭合与跨位置配对不同。 | 待证-无条件(由24.3/24.5) | logic | `UnifiedTheory/Zeta/ZeroLedger.lean` | “不同位置”需要 `s≠J(s)` hypothesis。 |
| 定义 24.7 | 本体零点 = 投影相消 + 本地净账 + 层级闭合。 | 待证-无条件(定义) | 24.1/19.2 | `UnifiedTheory/Zeta/OnticZero.lean` | 条件 (2) 是规范选择;不要当作所有 zeta 零点事实。 |
| 定理 24.8 | 本体零点必在中线,离线投影零点非本体零点。 | 待证-无条件(定义展开 + 19.3) | 19.3 | `UnifiedTheory/Zeta/OnticZero.lean` | 这是 conditional-on-definition,不是 RH。 |
| 定理 24.9 | 不引用乘性/正性的“闭合零点只在中线”命题会被仪器击杀。 | 纯叙事(方法论;可做 counterexample theorem if instrument formalized) | 24.5 instrument | `UnifiedTheory/Zeta/CounterInstrument.lean` | 需有精确命题 schema 才能形式化。 |
| 账目 24.10 | RH 等价于每个投影零点都是本体零点,桥为正性。 | 开叶子(周边可证:24.8 conditional、26.3显式公式、26.4正性等价) | `riemannZeta`, RH Prop需自建 | `UnifiedTheory/Zeta/RHBridge.lean` | RH 是真开叶子;只能定义 `RiemannHypothesis : Prop` 和周边等价/conditional。 |
| 定理 24.11 | 任意有限素数窗口 Euler 截断无零点,只有虚轴极点格。 | 待证-无条件 | finite products, `Complex.exp_eq_one_iff` | `UnifiedTheory/Zeta/FiniteWindows.lean` | `ζ_S=1/g_S` 是 meromorphic,Lean 中应表述为 denominator zeros,避免 partial functions。 |
| 推论 24.12 | 投影零点不可由任何有限素数窗口产生,相消是 tail+延拓现象。 | 待证-conditional(h=24.11 + analytic continuation definitions) | 24.11 | `UnifiedTheory/Zeta/FiniteWindows.lean` | “不可达”要精确为 finite truncation has no zeros,不是数值无法近似。 |

### 第二十五章 谱几何层

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 25.1 | `l2(A)` 内积完成和带标签向量所在子空间。 | 待证-无条件 | `lp`, Hilbert space APIs | `UnifiedTheory/Zeta/HilbertSpace.lean` | Formal product carrier 与 `l2` carrier 必须分离。 |
| 定理 25.2 | `||Z_vec(s)||^2=zeta(2sigma)`, iff `sigma>1/2` 收敛。 | 待证-conditional(h=zeta Dirichlet series convergence/divergence) | `riemannZeta`, summability of `n^-s` | `UnifiedTheory/Zeta/HilbertSpace.lean` | mathlib `riemannZeta` is analytic continuation; Dirichlet series theorem需确认。 |
| 定理 25.3 | 中线是 `l2` 边界。 | 待证-conditional(h=25.2 + harmonic divergence) | p-series/harmonic divergence | `UnifiedTheory/Zeta/HilbertSpace.lean` | `σ=1/2` 边界不是向量存在点。 |
| 定理 25.4 | 垂直运动为酉流,水平运动为耗散半群。 | 待证-无条件(once Hilbert carrier set) | diagonal operators on `lp` | `UnifiedTheory/Zeta/SpectralFlow.lean` | 无界 operator domain 是风险;可先做 coordinatewise theorem。 |
| 定理 25.5 | 再生核 `<Z(s),Z(w)>=zeta(s+conj w)` 和共振对合。 | 待证-conditional(h=absolute convergence Re(s+conj w)>1) | Dirichlet series, inner product | `UnifiedTheory/Zeta/ReproducingKernel.lean` | 共振极点在延拓核上,不一定是实际 `l2` inner product。 |
| 推论 25.6 | 镜像配对是谱层共振对。 | 待证-conditional(h=25.5) | 25.5 | `UnifiedTheory/Zeta/ReproducingKernel.lean` | 要明确“共振”= kernel pole condition。 |
| 定理 25.7 | 中线三重刻画统一。 | 待证-conditional(h=19.3 + 23.8 + 25.3/25.5) | previous | `UnifiedTheory/Zeta/CriticalLine.lean` | 这是合成定理,每个分量要分别已证。 |
| 评注 25.8 | Hilbert-Polya 自伴算子未构造。 | 开叶子(周边可证:25.4 diagonal flow;缺HP算子) | no | `UnifiedTheory/OpenProblems/HilbertPolya.lean` | 不要把现有 diagonal `Lhat` 混成零点谱算子。 |
| 前沿引注 25.9 | Hardy space of Dirichlet series 对应。 | 纯叙事(文献定位) | no | docs | 可引用但不需 Lean。 |
| 定理 25.10 | 一般热迹的半横标中线、范数、核、酉性普遍定理。 | 待证-conditional(h=热迹横标定义和收敛判别) | summability, Hilbert spaces | `UnifiedTheory/Zeta/GeneralHeatTrace.lean` | `alpha` 横标需精确定义为 abscissa,否则 theorem 不可检。 |
| 推论 25.11 | 三重刻画分解:反射中心=横标是函数方程实质。 | 待证-conditional(h=25.10) | 25.10 | `UnifiedTheory/Zeta/GeneralHeatTrace.lean` | “函数方程实质”是解释;formal part 是 `c=alpha` iff lines coincide。 |
| 定理 25.12 | 带标签 zeta 向量是除法算子的联合本征向量。 | 待证-无条件(on formal/l2 domain) | `Finsupp`, shifts on `lp` | `UnifiedTheory/Zeta/Bloch.lean` | 需限制 `σ>1/2` for `l2`; formal carrier可无条件。 |
| 定理 25.13 | `log p` 方向在有限素数相位环面稠密。 | 待证-无条件 | Kronecker/dense subgroup theorem, FTA | `UnifiedTheory/Zeta/Brillouin.lean` | 需 mathlib dense subgroup API;唯一分解给 Q-linear independence of `log p`。 |
| 评注 25.14 | 值层晶体与码层拟晶分层。 | 纯叙事(组织说明) | no | docs | 不形式化。 |
| 评注 25.15 | 两相与双时间解释。 | 纯叙事(解释) | no | docs | 不形式化。 |

### 第二十六章 桥通道

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定义 26.1 | 单地址状态和 von Mangoldt 账。 | 待证-无条件 | factorization support, `Nat.Prime` | `UnifiedTheory/Zeta/VonMangoldtLedger.lean` | 标准 `vonMangoldt` 若 mathlib 有需 survey;自建也可。 |
| 命题 26.2 | `-Z'/Z` 是单地址热迹。 | 待证-conditional(h=Euler product differentiability/log derivative) | Euler product, derivative of product; current mathlib unknown | `UnifiedTheory/Zeta/LogDerivative.lean` | 对数导数需要非零域和收敛交换。 |
| 定理 26.3 | 显式公式把单址账本累计与零点谱相联。 | 待证-conditional(h=ExplicitFormula for zeta/vonMangoldt) | 当前 mathlib 未见 explicit formula | `UnifiedTheory/Zeta/ExplicitFormula.lean` | 这是重型解析数论;应作为 hypothesis 后证明账本翻译。 |
| 账目 26.4 | RH 三面孔:参数面、Weil正性面、涨落面。 | 开叶子(周边可证:定义RH、conditional等价、有限检测器) | no direct mathlib confirmed | `UnifiedTheory/Zeta/RHBridge.lean` | 正性等价可 conditional;RH 本身不可证明。 |
| 定理 26.5 | zeta 是散射系统 S 矩阵,零点为相位跳。 | 待证-conditional(h=scattering interpretation + argument principle) | `completedRiemannZeta_one_sub`, argument principle需 survey | `UnifiedTheory/Zeta/Scattering.lean` | 物理散射字面化需定义 scattering object;否则只证明 unit modulus ratio。 |
| 评注 26.6 | 延迟有地址和相位二叶。 | 纯叙事(解释) | no | docs | 不形式化。 |
| 命题 26.7 | 编码拟晶衍射无条件;零点拟晶条件于 RH;衍射峰在 `log p^m`。 | 待证-conditional(h=model set diffraction + explicit formula + RH) | harmonic analysis/model sets; no direct mathlib | `UnifiedTheory/Zeta/Diffraction.lean` | “零点拟晶性 iff RH”需严格 measure/Fourier transform definitions。 |
| 评注 26.8 | 拟晶联系是通道不是定位之力。 | 纯叙事(方法论) | no | docs | 不形式化。 |
| 条目 26.9 | Li/Weil/CCM 有限化和正性检测器。 | 开叶子(周边可证:LiCriterion Prop、conditional alarm lemmas) | no direct mathlib confirmed | `UnifiedTheory/Zeta/PositivityCriteria.lean` | 前沿结果可作为 imported hypothesis;不要把数值仪器当 proof。 |
| 条目 26.10 | Jensen-Polya 检测器和渐近 RH。 | 待证-conditional(h=GORZ theorem) / 开叶子(全体Jensen=RH) | polynomial real-rootedness APIs | `UnifiedTheory/Zeta/JensenPolya.lean` | 已证渐近不等于全体 RH。 |

### 第二十七章 有限窗口与无穷

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定理 27.1 | 有限素数窗口有 Euclid 逃逸,有限读取有纤维。 | 已证@Arithmetic.EuclidEscape + Reading.Fibers(组成待包装) | 4.5, 8.5 | `UnifiedTheory/Zeta/FiniteInfinity.lean` | 合成 theorem 尚未存在;可直接包装。 |
| 定理 27.2 | 无穷由共尾窗口、tail预算、ledger闭合管理。 | 纯叙事(方法原则) | 12.6 | `UnifiedTheory/Kernel/Tail.lean` | 同 12.6,等号式不作数学等式。 |
| 定理 27.3 | 读数塔逆极限在手,证明塔极限不可公理化。 | 待证-conditional(h=10.6/20.12 + Tarski/Godel) | topology + mathematical logic | `UnifiedTheory/Tower/LimitComparison.lean` | 证明塔部分超出当前 mathlib;应参数化为 logic hypotheses。 |
| 评注 27.4 | RH 有初等 `Pi1` 形式,若假有限反驳。 | 待证-conditional(h=Lagarias criterion) / 开叶子(RH truth) | divisor sums/harmonic numbers; no direct mathlib confirmed | `UnifiedTheory/Zeta/RHPiOne.lean` | Lagarias 等价可引为 hypothesis;不能推出 RH。 |
| 评注 27.5 | 零点全知光学读法和双缝实性。 | 纯叙事(部分恒等式可拆) | `completedRiemannZeta` | `UnifiedTheory/Zeta/Optics.lean` | 光学比喻不进 theorem;核恒等式可独立证明。 |
| 评注 27.6 | 全知空间:泛点、算术景、F1;全知时间冻结。 | 纯叙事(前沿引注/哲学组织) | no | docs | 不形式化。 |
| 评注 27.7 | 神学属性核对、自指爬塔与信任。 | 纯叙事(分类学/前沿引注) | no | docs | 不形式化。 |
| 评注 27.8 | zeta 特殊值身份、正规化残差、p-adic 缝合、概率。 | 待证-conditional(h=special value theorems/Kummer/KL zeta) / 纯叙事 | `riemannZeta_zero`, special values maybe survey | `UnifiedTheory/Zeta/SpecialValues.lean` | 特殊值定理可证明/包装,但“DNA读法”为解释。 |
| 评注 27.9 | 四类特殊值与 mod 4 的 `chi4` 桥。 | 待证-conditional(h=two-square theta/L-series identities) | Dirichlet characters/LSeries | `UnifiedTheory/Zeta/ChiFour.lean` | Klein four vs cyclic four辨析是语义,公式可形式化。 |
| 评注 27.10 | 全知三张概率脸:黄金/GUE/Selberg。 | 待证-conditional(h=equidistribution/GUE/Selberg CLT) / 纯叙事 | probability/statistics; no direct zeta stats | `UnifiedTheory/Zeta/ProbabilityFaces.lean` | GUE/Selberg 是前沿/经典深定理,不可无条件自证。 |
| 评注 27.11 | 布尔概率塌缩、酉守恒、Kochen-Specker 禁止。 | 待证-conditional(h=KS/Gleason if imported) / 纯叙事 | linear algebra/projections | `UnifiedTheory/Logic/Probability.lean` | KS 属对照档,非内核经典账本定理。 |
| 评注 27.12 | RH 概率档案、密度版 RH、随机替身。 | 开叶子(周边可证:density theorems as hypotheses, Li/Weil detectors) | no direct mathlib confirmed | `UnifiedTheory/Zeta/RHProbability.lean` | 命题概率是信念层;不要形式化成客观 probability of RH。 |
| 评注 27.13 | RH 为假世界的投影通道和可见性不对称。 | 待证-conditional(h=Bohr-Landau/Rodgers-Tao/Li criterion) | no direct mathlib confirmed | `UnifiedTheory/Zeta/RHCounterfactual.lean` | “假必有限显形”依 `Pi1` 形式;检测器报警需精确定理。 |
| 评注 27.14 | 玩具贝叶斯可见概率。 | 纯叙事(模型计算) | probability arithmetic | docs | 不应纳入数学 tower theorem。 |
| 评注 27.15 | 全知库存:素数、加法、零点谱。 | 纯叙事(结构解释;部分 automorphism claim可证) | monoid automorphisms, Nat addition | `UnifiedTheory/Arithmetic/Automorphism.lean` | “只有素数”是 ontology reading;若证明乘法自同构需精确 carrier。 |
| 评注 27.16 | 遗忘如何再生时间。 | 纯叙事(信息论解释;玩具恒等式可证) | finite bits/entropy | docs | 不形式化为核心 theorem。 |
| 评注 27.17 | 全知既终且始,终余代数读法。 | 待证-conditional(h=final coalgebra model) / 纯叙事 | category theory | `UnifiedTheory/Completion/Coalgebra.lean` | final coalgebra需具体 functor,否则只是类比。 |
| 评注 27.18 | 单态、无发生子启发和对称之盲。 | 纯叙事(方法论; countermodel可形式化) | symmetric finite sets | docs | “对称不给定位”可用 toy theorem,但不是 RH progress。 |
| 评注 27.19 | `Omega -> zeta` 取迹流水线。 | 待证-conditional(h=trace-class/heat trace model) / 纯叙事 | trace/operator theory | `UnifiedTheory/Zeta/TracePipeline.lean` | `Tr e^{-sL}` 在无限维需收敛域。 |
| 评注 27.20 | 和路/积路两条变换及 Euler 乘积会合。 | thin-rewrap(纯包 `riemannZeta_eulerProduct`) / 纯叙事 | `riemannZeta_eulerProduct` | `UnifiedTheory/Zeta/EulerProduct.lean` | 会合 theorem 是 22.3,其余读法不形式化。 |
| 评注 27.21 | 创世/末日读法与两种叶状。 | 纯叙事 | no | docs | 不形式化。 |
| 评注 27.22 | 往返账、组合四型与不变量三层。 | 纯叙事(可拆有限 group action examples) | finite group actions | docs | 不核心。 |
| 评注 27.23 | 信息反号、反酉对称与线诞生。 | 待证-无条件(反酉 toy model) / 纯叙事 | complex conjugation, inner product | `UnifiedTheory/Zeta/Antiunitary.lean` | 反酉对称仍只给配对,不能给 RH。 |
| 评注 27.24 | 未解决声明: `J`-不变不等于含于 `Fix J`。 | 待证-无条件(toy counterexample) | set theory | `UnifiedTheory/Zeta/ReflectionZeros.lean` | 这是重要防错 lemma,建议形式化为 finite set counterexample。 |
| 评注 27.25 | 双端对账概率法则。 | 纯叙事(前沿方法接口) | no | docs | 不形式化。 |
| 评注 27.26 | 离线零点全知身份。 | 纯叙事/待证-conditional(h=explicit formula projections) | no direct | docs | 作为档案,不作 theorem。 |
| 评注 27.27 | 零点身份证、坑数、碰撞出生。 | 待证-conditional(h=argument principle/zero counting) / 纯叙事 | complex analysis | `UnifiedTheory/Zeta/ZeroCounting.lean` | 碰撞模型多为 toy/PT,需明确不是 zeta proof。 |
| 评注 27.28 | 不可判定性分类和 RH 逻辑坐标。 | 待证-conditional(h=logic formalization) / 纯叙事 | computability/logic | `UnifiedTheory/Logic/RHLogic.lean` | RH 独立性未知;只能分类可能性。 |
| 评注 27.29 | 虚对、桥方差与两种时间。 | 纯叙事 | no | docs | 不形式化。 |
| 评注 27.30 | 不等号即时间、第二定律、共振词典。 | 纯叙事(物理解释) | no | docs | 不形式化。 |
| 评注 27.31 | 决定论、自由与全知留白。 | 纯叙事(哲学/对角接口) | no | docs | 不形式化。 |
| 评注 27.32 | 时间分类、p-adic 主猜想和最后未决位。 | 待证-conditional(h=Iwasawa/main conjecture references) / 开叶子(RH位) | no direct | docs | 主猜想类比不属于当前 tower proof。 |
| 评注 27.33 | 内部之问、Goodstein 和楼层。 | 待证-conditional(h=Goodstein/Kirby-Paris) / 纯叙事 | logic not current | `UnifiedTheory/Logic/Goodstein.lean` | Goodstein PA不可证不等于 RH不可证。 |
| 评注 27.34 | Ostrowski、乘积公式、唯一非紧位。 | 待证-conditional(h=Ostrowski theorem/product formula) | number fields/adeles maybe survey | `UnifiedTheory/Adeles/Ostrowski.lean` | adeles/absolute values是大模块,可先作 hypothesis。 |
| 评注 27.35 | 极点、非紧与离线三道缝区分。 | 纯叙事(部分极点可证) | `completedRiemannZeta_residue_one` | docs | “官方泄压阀”是解释。 |
| 评注 27.36 | 离线零点双重档案。 | 纯叙事/待证-conditional(h=dBN/Rodgers-Tao) | no direct | docs | 不作 theorem。 |
| 评注 27.37 | 热时间假说与临界普适。 | 纯叙事(前沿对照) | no | docs | 不形式化。 |
| 评注 27.38 | PT 词典、度规正定与 Krein 燃料。 | 待证-无条件(toy finite-dimensional PT lemmas) / 纯叙事 | linear algebra, Hermitian forms | `UnifiedTheory/Linear/PTSymmetry.lean` | toy PT theorem不证明 zeta RH。 |
| 评注 27.39 | 倾向 RH 假的持仓档案。 | 纯叙事(信念账) | no | docs | 命题无概率;不形式化。 |
| 评注 27.40 | de Bruijn-Newman 零点气体与两体律。 | 待证-conditional(h=dBN heat flow theorem) / 纯叙事 | no direct | docs | dBN theory可作为 external hypothesis;非当前 mathlib。 |
| 评注 27.41 | Lee-Yang 家族和尾判据。 | 待证-conditional(h=Lee-Yang/Newman-Wu) / 纯叙事 | no direct | docs | 统计物理定理是同型支撑,不是 zeta bridge proof。 |
| 评注 27.42 | LP 类、Pólya-Schur、稳定算子、KS 先例。 | 待证-conditional(h=stability preserver theorems) / 纯叙事 | polynomial stability APIs maybe partial | docs | 军火库清单不等于对 Φ 开火。 |

### 第二十八章 内核主定理

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 定理 28.1 | `K` 满足 17 条主性质。 | 待证-conditional(h=各章目标已形式化) | all previous | `UnifiedTheory/MainTheorem.lean` | 当前只能做 theorem index;未完成章节不得合成 `closed`。 |
| 定理 28.2 | 四条元原则对理论自身成立,含载荷矩阵。 | 待证-conditional(h=load-bearing dependency graph + previous theorems) | graph/records | `UnifiedTheory/Meta/Principles.lean` | “删去分量失去陈述资格”是 syntax dependency,需形式化为 dependency audit。 |
| 推论 28.3 | 理论对自身执行诚实性元原则。 | 待证-conditional(h=28.2) | 28.2 | `UnifiedTheory/Meta/Principles.lean` | 不能早于 28.2。 |
| 评注 28.4 | 分类劳动的不可穷尽半与可收割半。 | 纯叙事(由8.5/16/17/24与结构定理组织) | no | docs | 可引用 theorem index。 |
| 评注 28.5 | 自我模型、因果定位、毕达哥拉斯归档。 | 纯叙事(哲学/模型解释) | no | docs | 不形式化。 |

### 第二十九章 开放账本

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| O-1 | 机器层参考实现与 Check 原型仍需证明助手内逐指令形式化。 | 待证-无条件(有限片段) / 开叶子(一般求值总性不取) | computability/syntax | `UnifiedTheory/SelfCode/Machine.lean` | 一般总终止不应作为目标;只做所需片段。 |
| O-2 | 塔的算术化与 Check 逐指令算术化。 | 待证-conditional(h=proof system/evaluator encoding) | logic/computability | `UnifiedTheory/Tower/Arithmetization.lean` | 属重型逻辑工程,不可用 informal encoding 替代。 |
| O-3 | semantic 一般分类四类。 | 纯叙事(分类账;可做 metadata enum) | no | `UnifiedTheory/Meta/SemanticStatus.lean` | 可编码分类,但“穷尽现存条目”需文档审计脚本。 |
| O-4 | `Σ∞` 拓扑、紧致、路径刚性、双对偶闭环。 | 待证-conditional(h=10/20拓扑目标) | topological group | `UnifiedTheory/Completion/Solenoid.lean` | 文档标 closed,但 Lean 尚未实现。 |
| O-5 | 双面不变量对角回传/独立控制。 | 开叶子(周边可证:6.11-6.59 字典、trace map scaffold、conditional RH拉回) | no direct | `UnifiedTheory/OpenProblems/O5.lean` | 真开放;字典由 ζ 构造不提供独立控制。 |
| O-6 | C3b/RH 正性桥。 | 开叶子(周边可证:26.3显式公式、26.4正性等价、Li/Jensen conditional) | no direct | `UnifiedTheory/OpenProblems/O6.lean` | 等价和检测器可形式化;正性本体不可假证。 |
| O-7 | 核内微分最小语义。 | 待证-无条件 | `HasDerivAt` or modulus derivative | `UnifiedTheory/Numbers/Derivative.lean` | 文档 closed,Lean 未建；mathlib derivative不完全忠实于带模数定义。 |
| O-8 | 逆账本由群化和成本时间闭合。 | 待证-无条件 | 18.10/18.11 | `UnifiedTheory/Dynamics/Groupified.lean` | 当前只有 EventHist length theorem。 |
| O-9 | 解析层核内重建四石。 | thin-rewrap(部分 zeta mathlib) / 待证-conditional(h=theta/Mellin rebuilt) | `completedRiemannZeta_one_sub`, `riemannZeta_one_sub` | `UnifiedTheory/Zeta/Completed.lean` | mathlib 已有 zeta continuation,但文档“核内重建”未在项目中完成。 |
| O-10 | 外部统一测试与盲测协议。 | 纯叙事(工程协议) | no | docs/scripts | 不属 Lean theorem。 |
| 评注 29.1 | O-5/O-6 与物理定理对照。 | 纯叙事(前沿对照) | no | docs | 不形式化。 |
| 评注 29.2 | 几何图景先例谱系。 | 纯叙事(文献定位) | no | docs | 不形式化。 |
| 评注 29.3 | 勘误账 E 系列。 | 纯叙事(审计记录;不应进入理论命名) | no | docs | 项目纪律不鼓励理论内保留编辑事故为 theorem。 |
| 评注 29.4 | 全息账本形式与 p-adic 树接口。 | 待证-conditional(h=Bruhat-Tits/tree model) / 纯叙事 | graph/tree math | `UnifiedTheory/Adeles/PAdicTree.lean` | 物理内容不认领。 |
| 评注 29.5 | 珠网性质的动力、观测、编码三化身。 | 待证-conditional(h=20.14/25.13/Sturmian repetition) / 纯叙事 | dynamics/combinatorics | `UnifiedTheory/Golden/SturmianRepetition.lean` | “因陀罗网”意象不形式化。 |
| 评注 29.6 | 概率读数、有限域两平方塌平、类域塔/Iwasawa 塔。 | 待证-conditional(h=finite field theorem + class field/Iwasawa results) / 纯叙事 | finite fields, algebraic number theory | `UnifiedTheory/Reading/FiniteFieldTwoSquares.lean` | 有限域两平方易证;类域塔是外部深定理。 |
| 评注 29.7 | 布尔概率、0-1律、逻辑归纳、Gleason。 | 待证-conditional(h=external logic/probability theorems) / 纯叙事 | probability/logic | `UnifiedTheory/Logic/Probability.lean` | 不把信念价格当数学真值概率。 |
| 评注 29.8 | 外部四次谱曲线论文对接。 | 待证-conditional(h=paper theorem statements) / 纯叙事 | polynomial/elliptic curve APIs | `UnifiedTheory/External/SpectralCurve.lean` | 外部论文可作 separate formal target,不是 PZG core prerequisite。 |

### 第三十章 最终压缩

| id | 一句话陈述 | 分类 | mathlib 支撑 | 建议模块 | 忠实性风险 |
|---|---|---|---|---|---|
| 第三十章压缩句 | 全塔以生成、编码、读数、账本、相位、隐藏纤维、完成化、内化塔和 zeta/RH 最后一桥压缩。 | 纯叙事(最终摘要) | all previous | docs/theorem index | 只作索引摘要;不要创建单一“证明全书”的 theorem。 |

## B. 蕴含图

### 地基到 PZG

- ch1 `Mark/sigma` -> ch16 diagonal: `sigma` 提供对角反转的两值操作。
- ch2 history/event -> ch18 trajectory/cost: 生成历史给轨道数据和成本箭头。
- ch3 Newman criterion -> ch5 PZG normalization/ch9 norm/ch19 phase: “单位性”作为唯一标准形、唯一编码、单位相位的通用模式。
- ch4 FTA/free prime axes -> ch5 PZG table: `PrimeExp ≃ Nat+` 与每轴 Zeckendorf 给 `PZGTable ≃ Nat+`。
- ch4 Euclid escape + ch8 finite reading -> ch12 tail -> ch27 finite-window limits.

### PZG 到黄金双面和 O-5

- ch5 Zeckendorf + ch6.3 double-face lift -> ch6.4 `lambdaPlus/lambdaMinus`.
- ch6.21 carry identities + ch6.22 deficit integer -> ch6.25 trichotomy -> ch6.26 almost additivity.
- ch6.44 Beatty shift -> ch6.45 phase判读 -> ch6.46 deficit distribution -> ch29.6 probability reading.
- ch6.12 `Z_qc` abscissa ⇐ ch6.7 model set + ch6.8 multiplicativity.
- ch6.14 first factorization ⇐ ch6.12 Euler product + first bit extraction.
- ch6.19 second cascade ⇐ ch6.14 + golden cancellation `phi^4=phi^3+phi^2`.
- ch6.32 pullback RH form ⇐ ch6.19 divisor identity + zeta reflection + zeta zero-free line `Re=1`.
- O-5 open leaf = “independent analytic control of `Z_qc`/shift surface”, not the factorization dictionary itself.
- Conditional theorem shape:
  - `theorem qc_pullback_of_dictionary (hDict : QCDivisorIdentity) : RHRightBand ↔ QCZerosOnPullbackLine`.
  - `theorem rh_of_independent_qc_control (hCtrl : QCIndependentLineControl) : RiemannHypothesis`.

### 读数、完成与动力学

- ch8 finite windows + CRT -> ch10 profinite completion `Zhat`.
- ch10 `Zhat ≅ prod_p Z_p` + duality -> ch20 solenoid flow and hidden rigidity.
- ch18 prime-address state + ch19 phase -> ch25 Hilbert-space heat trace.
- ch20 path rigidity -> ch27/29 “parallel lines indistinguishable by finite windows” narrative; formal core is ch20.10/20.14.

### Zeta/RH 主桥

- ch22.1 heat trace ⇐ ch5 PZG bijection + ch18 length `L=log n`.
- ch22.3 Euler product ⇐ ch4 free prime axes; mathlib support `riemannZeta_eulerProduct`.
- ch23 completion/function equation ⇐ mathlib `completedRiemannZeta_one_sub` or conditional theta/Mellin rebuild.
- ch24 zero ledger:
  - projected zero = `riemannZeta rho = 0` or completed zero.
  - ontic zero = projected zero + local scale account zero.
  - ch24.8 `OnticZero rho -> rho.re=1/2` is definitional and unconditional after 19.3.
- ch24.10 RH bridge:
  - `RiemannHypothesis := forall rho, NontrivialZero rho -> rho.re = 1/2`.
  - `EveryProjectedZeroOntic -> RiemannHypothesis` via ch24.8.
  - `RiemannHypothesis -> EveryProjectedZeroOntic` only because ontic condition is `rho.re=1/2` plus projected zero; formal equivalence is definitional after choosing nontrivial zero set.
  - The hard part is not this equivalence, but proving every projected zero satisfies the local/positive condition from arithmetic input.
- ch26 explicit formula channel:
  - `ExplicitFormula` connects single-address/von Mangoldt ledger to zero spectrum.
  - `WeilPositivity` on convolution-square tests ⇔ RH.
  - Li/Jensen/finite-window criteria are conditional detectors around the same open leaf.
- True open leaf:
  - `RiemannHypothesis`.
  - Equivalent open formulations: `WeilPositivity`, `LiAllNonnegative`, `JensenAllHyperbolic`, `EveryProjectedZeroOntic`, `NoOffLineZeros`, suitable `Q_n>=0` finite-window family.

### 主定理

- ch28.1 is not a new mathematical theorem until every listed dependency has a Lean theorem or an explicit hypothesis.
- ch28.2 load-bearing matrix can be formalized as a dependency graph audit:
  - each component has a target theorem whose statement references that component.
  - removing a component means the statement is not typeable, not that Lean proves a counterfactual.

## C. 建议形式化顺序

1. **Inventory wrappers and status hygiene**  
   前置: none. 难度: easy mathlib-tractable.  
   建 `UnifiedTheory/FormalStatus.lean` 或文档索引,列出 source id -> Lean target。先把当前已证目标和 statement-only `DeficitTrichotomy` 区分清楚。

2. **Foundation closure wrappers**  
   前置: existing foundation modules. 难度: easy.  
   包装 4.2/4.3, 5.2, 8.3/8.4, 9.1-9.5, 13.2 的基础 theorem,尽量用 mathlib。

3. **Full two-square chapter**  
   前置: 4.4, CRT/ZMod, mathlib sum-two-squares. 难度: medium.  
   把当前素数版 `prime_sq_add_sq_iff` 扩成文档 9.10 的一般自然数版;若要忠实证明,补 Wilson/Thue/Brahmagupta 链。

4. **Window/tail framework**  
   前置: 8章、12章 definitions. 难度: medium.  
   定义 `Window`, `Cofinal`, `TailCert`, `TailClosed`, `LedgerEntry`;证明 tail 可加、围合、Euclid tail。

5. **Ledger identity and state layer**  
   前置: PZG decode/normalize, LedgerStatus. 难度: medium.  
   定义 `KernelObject`, `Code`, `=_K`, `State`, `Exponent update`, `Length`. 证明 7.3, 18.3/18.5/18.7 的忠实版本。

6. **Groupified dynamics and cost arrow**  
   前置: 18 state/length. 难度: medium.  
   做 `PrimeZExp : ℕ ->₀ ℤ`, `Q+` product map, cost variation;证明 18.10/18.11/18.12。

7. **Phase and critical line algebra**  
   前置: length. 难度: easy-medium.  
   定义 `Phi_s`, half-density, local scale, `J(s)=1-conj s`;证明 19.3-19.5, 24.3/24.4/24.8。

8. **Golden deficit completion**  
   前置: existing Golden modules. 难度: medium.  
   证明 6.25, 6.26, 6.44, 6.45。优先用 Beatty 公式路线,把 `DeficitTrichotomy : Prop` 升成 theorem。

9. **Golden finite combinatorics / trace-map finite core**  
   前置: 6.44/6.45. 难度: medium-hard.  
   做 6.35/6.36 完整坐标版、6.48-6.50、6.53/6.54/6.59 的形式级数簿记。

10. **Profinite and solenoid definitions**  
    前置: CRT/window. 难度: hard topology.  
    选用 mathlib 的 `ZMod`, `PadicInt`, inverse limit/product topology。先证明有限满足与 `Zhat` carrier,再处理 10.3, 10.6, 10.8, 20.3, 20.10, 20.12。

11. **Self-code and tower scaffold**  
    前置: PZG encoding, syntax datatype. 难度: hard logic engineering.  
    定义 ISA, syntax, encoder, evaluator fragment, `Sub`;证明直线片段总终止、Cantor closure theorem wrapper。一般 U-dependent theorems保留 precise hypotheses。

12. **Numbers and derivative predicates**  
    前置: none beyond mathlib. 难度: easy-medium.  
    对 21.1 作 thin wrappers;定义 modulus derivative or map to `HasDerivAt` with equivalence theorem if desired。

13. **Zeta heat trace wrappers**  
    前置: PZG + length. 难度: medium.  
    定义 `ZK` on `Re s>1`,证明与 `riemannZeta` 的 Dirichlet series wrapper;包装 `riemannZeta_eulerProduct`。

14. **Completion/function equation wrappers**  
    前置: zeta wrappers. 难度: medium if thin; hard if rebuilding theta/Mellin.  
    Thin route: use `completedRiemannZeta`, `completedRiemannZeta_one_sub`, `riemannZeta_one_sub`. Rebuild route: 10.10 finite Poisson -> theta -> Mellin.

15. **Tagged vector and Hilbert geometry**  
    前置: heat trace, length. 难度: hard analysis.  
    Build formal carrier and `l2` carrier; prove 22.5/22.6, 25.2-25.7, 25.10-25.13 with convergence hypotheses where needed.

16. **Finite zeta windows**  
    前置: Euler factors. 难度: medium.  
    Prove 24.11 exactly for finite prime products as denominator-zero statements; derive 24.12.

17. **Quasicrystal zeta dictionary**  
    前置: golden combinatorics, zeta Euler product. 难度: hard analysis.  
    Define `Z_qc`, `ShiftSurface`, formal Euler products, first/second cascade, pullback line. Treat divisor identities as conditional until convergence domains are proved.

18. **Explicit formula and positivity interfaces**  
    前置: zeta completion. 难度: open-leaf-encoding/hard analytic.  
    Define `ExplicitFormula`, `WeilPositivity`, `LiCriterion`, `JensenPolyaCriterion`, `RiemannHypothesis`. Prove equivalence theorems conditional on classical analytic hypotheses; do not assert RH.

19. **Open account modules**  
    前置: all above. 难度: mixed.  
    Encode O-1/O-2/O-5/O-6/O-10 as precise `Prop` definitions and theorem stubs only when they have meaningful conditional周边定理。No `True.intro`.

20. **Main theorem index**  
    前置: target wrappers complete. 难度: easy once dependencies exist.  
    Build `MainTheorem` as a structure collecting theorem fields, not as one giant proof that silently assumes missing leaves.

## D. 诚实小结

粗略按本 gap map 的编号项计:

- 项目内已证或已编码的核心条目约 35-45 条,集中在 ch1-5、ch6 的 `PhiInt/deficit integer/carry finite heart`、ch8 fiber、ch9 prime two-square wrapper、ch16 Cantor影子、ch18 cost length影子。
- 可无条件证明但尚未进入项目的条目约 90-110 条,主要是 wrapper、ledger/state/tail框架、完整二平方链、相位代数、黄金 Beatty/形式级数簿记、有限窗口定理。
- 适合 conditional 形式化的条目约 55-75 条,主要是拓扑对偶、solenoid path lifting、theta/Mellin重建、显式公式、散射、深解析数论和外部前沿定理接口。
- 真开叶子很少但承重: O-5 独立 `Z_qc` 解析控制、O-6/RH 正性桥、RH 本身及其等价正性/全体检测器形式。它们周围有大量可机器验证的 conditional 定理。
- 纯叙事/语义/前沿对照条目约 60 条以上,尤其 ch27 和 ch29。它们适合做索引和 metadata,不应消耗 theorem 预算,也不应作为 Lean 证明目标。

真实可达边界: 整座塔的对象、依赖、conditional 架构、绝大多数有限/代数/组合/账本内容都可以在 mathlib-based 线中系统形式化。不可达的不是“整座塔”,而是少数明确叶子: RH/Weil 正性与 O-5 的独立解析控制。正确施工方式是把这些叶子定义成精确 `Prop`,并把所有通向它们和从它们推出的桥定理做成 conditional theorem。
