import Mathlib

namespace UnifiedTheory

open Real

/-- `φ³ = 2φ + 1`。 -/
theorem goldenRatio_cube : goldenRatio ^ 3 = 2 * goldenRatio + 1 := by
  linear_combination (goldenRatio + 1) * Real.goldenRatio_sq

/-- `φ⁴ = 3φ + 2`。 -/
theorem goldenRatio_pow4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  linear_combination
    (goldenRatio ^ 2 + goldenRatio + 2) * Real.goldenRatio_sq

/-- **心脏小章一页代数(旗标恒等)**:`φ⁴ + φ² − 1 = 2φ³`。 -/
theorem goldenRatio_pow4_add_sq_sub_one :
    goldenRatio ^ 4 + goldenRatio ^ 2 - 1 = 2 * goldenRatio ^ 3 := by
  rw [goldenRatio_pow4, goldenRatio_cube, Real.goldenRatio_sq]
  ring

/-- **二阶级联黄金相消(命题 6.19)**:`φ² + φ³ = φ⁴`。 -/
theorem goldenRatio_sq_add_cube :
    goldenRatio ^ 2 + goldenRatio ^ 3 = goldenRatio ^ 4 := by
  rw [Real.goldenRatio_sq, goldenRatio_cube, goldenRatio_pow4]
  ring

/-- **Zeckendorf 禁 11 之解析影(定理 6.23)**:`φ⁴ − φ³ − φ² = 0`。 -/
theorem goldenRatio_pow4_sub_cube_sub_sq :
    goldenRatio ^ 4 - goldenRatio ^ 3 - goldenRatio ^ 2 = 0 := by
  rw [goldenRatio_pow4, goldenRatio_cube, Real.goldenRatio_sq]
  ring

/-- `ψ = −1/φ`(共轭即负倒数)。 -/
theorem goldenConj_eq_neg_inv : goldenConj = -1 / goldenRatio := by
  rw [div_eq_mul_inv, Real.inv_goldenRatio]
  ring

/-- `1/φ = φ − 1`。 -/
theorem goldenRatio_inv_eq : 1 / goldenRatio = goldenRatio - 1 := by
  rw [one_div, Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

/-- **C₀ 两枚半黄金(拆分)**:`φ/2 = √5/2 − 1/(2φ)`。 -/
theorem goldenRatio_half_eq_sqrt5_half_sub :
    goldenRatio / 2 = Real.sqrt 5 / 2 - 1 / (2 * goldenRatio) := by
  have hφ : (goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hsqrt : Real.sqrt 5 = 2 * goldenRatio - 1 := by
    change Real.sqrt 5 = 2 * ((1 + Real.sqrt 5) / 2) - 1
    ring
  have hhalf_inv : 1 / (2 * goldenRatio) = (goldenRatio - 1) / 2 := by
    calc
      1 / (2 * goldenRatio) = (1 / goldenRatio) / 2 := by
        field_simp [hφ]
      _ = (goldenRatio - 1) / 2 := by
        rw [goldenRatio_inv_eq]
  rw [hhalf_inv, hsqrt]
  ring

/-- **Binet 逐位恒等(r̄-链之种,观察 6.146(二))**:`F_{k+1}/φ = F_k − ψ^{k+1}`。 -/
theorem fib_succ_div_goldenRatio (k : ℕ) :
    (Nat.fib (k + 1) : ℝ) / goldenRatio = (Nat.fib k : ℝ) - goldenConj ^ (k + 1) := by
  have hφ : (goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hmul : goldenRatio * goldenConj ^ (k + 1) = -goldenConj ^ k := by
    calc
      goldenRatio * goldenConj ^ (k + 1) = (goldenRatio * goldenConj) * goldenConj ^ k := by
        rw [pow_succ']
        ring
      _ = -goldenConj ^ k := by
        rw [Real.goldenRatio_mul_goldenConj]
        ring
  rw [div_eq_iff hφ]
  nlinarith [Real.fib_succ_sub_goldenRatio_mul_fib k, hmul]

/-- **c\* 恒等(钉一,源 6.145(一))**:`φ² + 1 = √5·φ`(= c\*)。 -/
theorem cstar_eq_sqrt5_phi : goldenRatio ^ 2 + 1 = Real.sqrt 5 * goldenRatio := by
  have hsqrt : Real.sqrt 5 = 2 * goldenRatio - 1 := by
    change Real.sqrt 5 = 2 * ((1 + Real.sqrt 5) / 2) - 1
    ring
  rw [hsqrt]
  nlinarith [Real.goldenRatio_sq]

/-- **双面长度整性(Binet 差,源 6.4)**:`φⁿ − ψⁿ = √5·Fₙ`。
故双面长度 `ℓ(z) = (λ₊−λ₋)/√5` 为整 Fibonacci 权,而非无理黄金权。 -/
theorem goldenPow_sub_goldenConjPow (n : ℕ) :
    Real.goldenRatio ^ n - Real.goldenConj ^ n = Real.sqrt 5 * (Nat.fib n : ℝ) := by
  rw [Real.coe_fib_eq n]
  have h5 : Real.sqrt 5 ≠ 0 := by positivity
  field_simp [h5]

/-- **双面取向符号(源 6.4)**:`φⁿ·ψⁿ = (−1)ⁿ`(因 `φ·ψ = −1`)。
这是 r̄-链振荡的交错符号。 -/
theorem goldenPow_mul_goldenConjPow (n : ℕ) :
    Real.goldenRatio ^ n * Real.goldenConj ^ n = (-1 : ℝ) ^ n := by
  rw [← mul_pow, Real.goldenRatio_mul_goldenConj]

/-- **双面迹(Lucas 迹,源 6.4)**:`φⁿ + ψⁿ = 2·F_{n+1} − F_n`(黄金旋转之迹 = Lucas 数,整值)。
补齐特征值对称函数之三元组:差(`√5·Fₙ`)、积(`(−1)ⁿ`)、和(Lucas 迹)。 -/
theorem goldenPow_add_goldenConjPow (n : ℕ) :
    Real.goldenRatio ^ n + Real.goldenConj ^ n = 2 * (Nat.fib (n + 1) : ℝ) - (Nat.fib n : ℝ) := by
  have hφ2 : 2 * Real.goldenRatio - 1 = Real.sqrt 5 := by rw [Real.goldenRatio]; ring
  have hψ2 : 2 * Real.goldenConj - 1 = -Real.sqrt 5 := by rw [Real.goldenConj]; ring
  have h5 : Real.sqrt 5 ≠ 0 := by positivity
  rw [Real.coe_fib_eq (n + 1), Real.coe_fib_eq n, pow_succ Real.goldenRatio n,
    pow_succ Real.goldenConj n]
  field_simp
  linear_combination (Real.goldenRatio ^ n) * hφ2 - (Real.goldenConj ^ n) * hψ2

/-- **自相似 no-go(源定理 6.2)**:不存在几何比 `Λ` 使 `F_{k+2} = Λ·F_{k+1}` 对所有 `k` 成立
(相邻 Fibonacci 比 `F_{k+1}/F_k = 1, 2, 3/2, …` 非常数)。这是双面提升(6.3)之必要性:
没有单一几何权重能复现 Zeckendorf 取值,故需二维本征提升。 -/
theorem no_geometric_fib_ratio :
    ¬ ∃ Λ : ℝ, ∀ k : ℕ, (Nat.fib (k + 2) : ℝ) = Λ * (Nat.fib (k + 1) : ℝ) := by
  rintro ⟨Λ, h⟩
  have h0 := h 0
  have h1 := h 1
  norm_num [Nat.fib] at h0 h1
  linarith

/-- **Cassini 恒等式(黄金/Fibonacci 代换矩阵 unimodular 之根据)**:
`$F_{n+2}\,F_{n}-F_{n+1}^{2}=(-1)^{n+1}$`(整数)。等价于 `$\det(M^{n+1})=(\det M)^{n+1}=(-1)^{n+1}$`,
其中 `$M=\begin{psmallmatrix}1&1\\1&0\end{psmallmatrix}$` 是黄金/Fibonacci 代换矩阵。这 ground GPS
三角的维数群层:`$M$` unimodular(`$\det M=-1$`)⟹ 稳态 Bratteli–Vershik 维数群 `$\mathbb Z[\varphi]$`
为秩-2 unimodular 对象,其序单位映到 `$1$`、第二生成元映到 `$\varphi$`(SOE 强轨道等价不变量,
与谱 gap-labelling 群同一物)。 -/
theorem fib_cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2
      = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num [Nat.fib_zero, Nat.fib_one, Nat.fib_two]
  | succ n ih =>
      have hpow : ((-1 : ℤ)) ^ (n + 1 + 1) = -((-1) ^ (n + 1)) := by
        rw [pow_succ]; ring
      have hc : (Nat.fib (n + 2) : ℤ) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := n)
      have hd : (Nat.fib (n + 3) : ℤ) = (Nat.fib (n + 1) : ℤ) + (Nat.fib (n + 2) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := n + 1)
      show (Nat.fib (n + 3) : ℤ) * (Nat.fib (n + 1) : ℤ) - (Nat.fib (n + 2) : ℤ) ^ 2
        = (-1) ^ (n + 1 + 1)
      rw [hpow, hd, hc]
      rw [hc] at ih
      linear_combination -ih

/-- **Fibonacci/黄金代换矩阵的 Q-矩阵幂**:`$M^{n+1}=\begin{psmallmatrix}F_{n+2}&F_{n+1}\\F_{n+1}&F_n\end{psmallmatrix}$`,
其中 `$M=\begin{psmallmatrix}1&1\\1&0\end{psmallmatrix}$` 是黄金/Fibonacci 代换矩阵。这是代换矩阵 `$M$`
(GPS 三角维数群的稳态归纳极限映射)与 Fibonacci 数之间的具体链:`$M$` 的迭代恰生成 Fibonacci
序列,`$\det M=-1$` 经此给出 Cassini `\lean{UnifiedTheory.fib\_cassini}`,`$M$` 的特征多项式
`$x^2-x-1$` 的根 `$\varphi,\psi$` 即扩张/Galois-收缩(Pisot gap `$|\psi|=1/\varphi$`)方向。 -/
theorem fib_qmatrix_pow (n : ℕ) :
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ (n + 1)
      = !![(Nat.fib (n + 2) : ℤ), (Nat.fib (n + 1) : ℤ);
           (Nat.fib (n + 1) : ℤ), (Nat.fib n : ℤ)] := by
  induction n with
  | zero =>
      rw [pow_one]
      norm_num [Nat.fib_one, Nat.fib_two]
  | succ n ih =>
      have hd' : (Nat.fib (n + 2) : ℤ) + (Nat.fib (n + 1) : ℤ) = (Nat.fib (n + 3) : ℤ) := by
        have h : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
        rw [h]; push_cast; ring
      have hc' : (Nat.fib (n + 1) : ℤ) + (Nat.fib n : ℤ) = (Nat.fib (n + 2) : ℤ) := by
        have h : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
        rw [h]; push_cast; ring
      rw [pow_succ, ih, Matrix.mul_fin_two]
      simp only [mul_one, mul_zero, add_zero]
      rw [hd', hc']

end UnifiedTheory
