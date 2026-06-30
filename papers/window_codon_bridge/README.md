# Window6 ↔ Codon-Q₆ 桥梁

本分支(`feat/window-codon-bridge`)的使命:在**抽象数学的 forced Window6 结构**(fibonacci_reality)与**生物的 codon-Q₆ 边界结构**(bio_reality)之间,产出**forced-correspondence 证书**,并与 bio 数据分支**双向通讯**。

**不是又一条数据管线。** 它是"数学↔生物" forcing 证书工厂,跟 bio 分支配合:桥发可证伪的结构猜想 → bio 用数据检验;bio 的结构性发现 → 引导桥去推导其根源。

---

## 两侧载体(各自论文已建好,但都明确拒绝过桥)

**数学侧** — `fibonacci_reality/parts/forced_window_structure/`(width-6 无相邻-1 布尔词 = Fibonacci/Zeckendorf):
- 窗口词数 **X₆ = 21 = F₈**。
- 4-cell 粗 Markov 核,cells `U₂,U₁,U_L,U_R` 基数 `27,22,9,6`,边矩阵 E,行归一核 T;谱 = **低能基态(leading)+ 高能模(sub-leading)的叠加**,Fibonacci-leading 系数与 golden 比相关。(`window6-markov-kernel-coarse-spectrum-fibonacci-leading`)
- **Foldbin / 二次折叠**:width-6 horizon 有 seam `s₆=7`、return depth `ρ₆=10`;Foldbin 尾立方 **3 个自由布尔坐标 c₇c₈c₉**,别名 `F₈,F₉,F₁₀=21,34,55`;`ρ₆−s₆=3`。尾部折回窗口。(`window6-fibonacci-horizon-seam-return-foldbin-unification`)
- 其它:edge-flux mod-3 障碍、mod-p* **571** 谱碰撞、Smith normal form cokernel、transfer operator golden Perron 谱、Parry measure。

**生物侧** — `bio_reality/parts/codon_window_reality_boundary/window_six_codon_tiles_at_the_code_layer`(codon cube Q₆,64=2⁶):
- 边界集 **R,|R| = 13 = F₇**,face count `(13,16,4)`(穿孔立方体);**21 个同义家族**。
- 谱标量 **λ_M=0.675, λ_R=0.476, μ=3.05**,radial cubic check ≈ 0。

**两边都在自己有限载体上停下,各留了"需要单独证书/接触"的口子。本分支造那张证书。**

---

## 三个对应(桥的靶子)

| # | 数学 Window6 | 生物 codon Q₆ | 类型 |
|---|---|---|---|
| BC1 基数 | X₆=21=F₈;Fibonacci horizon | 21 同义家族;\|R\|=13=F₇ | 计数 forcing |
| BC2 谱 | Markov 核 T 特征值(高/低能叠加) | λ_M/λ_R/μ | 谱 forcing |
| BC3 折叠 | Foldbin 尾立方 3 自由坐标(seam-return) | 密码子 3 位 / wobble / Q^(2) 二次折叠 | 结构 forcing |

## 三个可证伪 forcing 猜想

- **BC1**:codon 边界基数(\|R\|=13、21 家族)是否被 Window6 Fibonacci horizon **forced**?需给出显式结构映射 `标准码边界 → width-6 Fibonacci 词`,证明 13/21 是必然而非巧合。bio 经验接触:R 在真实生物里有无签名(见 ledger,Route L 正测)。
- **BC2**:bio λ_M/λ_R/μ 是否 = Window6 粗 Markov 核 T(或密码子图的某粗粒化)的特征值?直接算 T 谱与 `0.675/0.476/3.05` 比。
- **BC3**:Foldbin 尾立方(3 自由坐标)是否对应密码子 3 位 / wobble 折叠;bio 的 Q^(2) 二次结构(Route B)是否为第二折叠的生物像。

## 证书 vs numerology(铁律)

- **forced-correspondence 证书** = 两个有限载体之间的**显式结构映射** + **forcing 论证**(给定数学结构 + 映射,生物量是**必然的**)。
- **禁止**:把 φ / 571 / Z₆ 当数值巧合移植进生物。**一个数字吻合(如 13=F₇)是写证书的提示,不是证书本身。** 这与 BEDC NameCert 纪律一致。
- 每个 BC 的产出要么是 `certified`(给出 forcing 论证),要么 `refuted`(映射不存在/谱不符),要么 `coincidence`(数字吻合但无结构 forcing)—— 后者必须**显式标注为 coincidence,不得当成果**。

## 双向通讯协议

`bridge_ledger.jsonl` —— 每行一条:
`{id, direction: "bridge->bio"|"bio->bridge", item, status: proposed|testing|supported|refuted|certified|coincidence, linked_bio_experiment, linked_certificate, note}`

- **bridge→bio**:桥发结构猜想 → orchestrator 在 bio 分支派对应数据实验 → 结果回填 ledger。
- **bio→bridge**:bio 的结构性发现(如 Route K「最优密码子方向按 GC3 聚类 + 弱普适核」、谱 λ_M/λ_R/μ)→ 成为桥的推导靶子。
- ledger 随 dev rollup 让两分支都可见;orchestrator(Claude)主动在两边搬运。

## 推导执行

桥的推导用 codex(像 BEDC 那套:LaTeX/Lean + 结构论证),orchestrator 编排 + **严防 numerology**。fibonacci 的 Window6 数学**只读**引用,不改其分支。
