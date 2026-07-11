import UnifiedTheory.Golden.Deficit
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# ch6.7/6.25 收缩面窗口界 → 亏空三值(无条件)

证明收缩面读数的对称界 `|β₋(encode n)| ≤ 1/φ`,据此把亏空三值 6.25 转为**无条件定理**
`deficitInt ∈ {−1,0,1}`(不再依赖 `MinusWindow` 假设)。

路线:`β₋(encode n)=Σ_{i∈l} ψ^i`(合法 Zeckendorf 词,指标 ≥2、gap≥2、降序)。三角不等式给
`|β₋| ≤ Σ_{i∈l} |ψ|^i`,`|ψ|=1/φ=:r`。对升序化的 `l.reverse` 用几何归纳
`geomBound`(升序 gap≥2 链 ⟹ `Σ r^i ≤ r^b/(1−r²)`),取 `b=2` 得 `≤ r²/(1−r²)`。
关键代数:`r=1/φ` 时 `r+r²=(φ+1)/φ²=1`,故 `1−r²=r`,`r²/(1−r²)=r`。
三值:`|k|=|μ(v)+μ(w)−μ(v+w)| ≤ 3/φ < 2`(因 φ>3/2),与整性相交 ⟹ `k∈{−1,0,1}`。
-/

namespace UnifiedTheory

open scoped BigOperators

/-- **几何归纳界**:升序 gap≥2 链、首元 ≥ b,则 `Σ_{i∈m} r^i ≤ r^b/(1−r²)`。
纯 List 归纳 + 实数算术,不用 tsum/Finset。 -/
theorem geomBound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr2 : r ^ 2 < 1) :
    ∀ (m : List ℕ) (b : ℕ), m.IsChain (fun a c => a + 2 ≤ c) →
      (∀ x ∈ m.head?, b ≤ x) →
      (m.map (fun i => r ^ i)).sum ≤ r ^ b / (1 - r ^ 2) := by
  have hden : 0 < 1 - r ^ 2 := by linarith
  intro m
  induction m with
  | nil => intro b _ _; simp only [List.map_nil, List.sum_nil];
           exact div_nonneg (pow_nonneg hr0 b) (le_of_lt hden)
  | cons a m' ih =>
    intro b _ hhead
    have hba : b ≤ a := hhead a (by simp)
    rw [List.isChain_cons] at *
    rename_i hchain
    obtain ⟨hrel, hchain'⟩ := hchain
    have hm' : (m'.map (fun i => r ^ i)).sum ≤ r ^ (a + 2) / (1 - r ^ 2) :=
      ih (a + 2) hchain' hrel
    have hpow : r ^ (a + 2) = r ^ a * r ^ 2 := by rw [pow_add]
    have hra : r ^ a ≤ r ^ b := pow_le_pow_of_le_one hr0 hr1 hba
    simp only [List.map_cons, List.sum_cons]
    have hkey : r ^ a + r ^ (a + 2) / (1 - r ^ 2) = r ^ a / (1 - r ^ 2) := by
      rw [hpow]; field_simp; ring
    calc r ^ a + (m'.map (fun i => r ^ i)).sum
        ≤ r ^ a + r ^ (a + 2) / (1 - r ^ 2) := by linarith
      _ = r ^ a / (1 - r ^ 2) := hkey
      _ ≤ r ^ b / (1 - r ^ 2) := (div_le_div_iff_of_pos_right hden).mpr hra

/-- `|ψ| = 1/φ`(收缩面比率)。 -/
theorem abs_goldenConj : |Real.goldenConj| = Real.goldenRatio⁻¹ := by
  rw [abs_of_neg Real.goldenConj_neg]; exact Real.inv_goldenRatio.symm

/-- **收缩面对称窗口界**:`|β₋(encode n)| ≤ 1/φ`。 -/
theorem abs_betaMinus_le (n : ℕ) :
    |AxisWord.betaMinusReal (AxisWord.encode n)| ≤ 1 / Real.goldenRatio := by
  have hφpos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hφ1 : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hφne : Real.goldenRatio ≠ 0 := ne_of_gt hφpos
  have hrmul : Real.goldenRatio⁻¹ * Real.goldenRatio = 1 := inv_mul_cancel₀ hφne
  have hr0 : (0 : ℝ) ≤ Real.goldenRatio⁻¹ := inv_nonneg.mpr (le_of_lt hφpos)
  have hrlt1 : Real.goldenRatio⁻¹ < 1 := by nlinarith [hrmul, hφ1, hr0]
  have hr1 : Real.goldenRatio⁻¹ ≤ 1 := le_of_lt hrlt1
  have hr2 : (Real.goldenRatio⁻¹) ^ 2 < 1 := by nlinarith [hrlt1, hr0]
  -- structural facts from Zeckendorf
  set l := (AxisWord.encode n).1 with hldef
  have hzeck : (l ++ [0]).IsChain (fun a b => b + 2 ≤ a) := (AxisWord.encode n).2
  haveI : Trans (fun a b : ℕ => b + 2 ≤ a) (fun a b : ℕ => b + 2 ≤ a)
      (fun a b : ℕ => b + 2 ≤ a) := ⟨fun {a b c} h1 h2 => by omega⟩
  have hpair : (l ++ [0]).Pairwise (fun a b => b + 2 ≤ a) := hzeck.pairwise
  rw [List.pairwise_append] at hpair
  obtain ⟨hpairL, _, hcross⟩ := hpair
  have hall : ∀ i ∈ l, 2 ≤ i := by
    intro i hi; have := hcross i hi 0 (by simp); omega
  have hnodup : l.Nodup := hpairL.imp (fun {a b} h => by omega)
  have hrev : l.reverse.IsChain (fun a c => a + 2 ≤ c) := by
    apply List.Pairwise.isChain
    rw [List.pairwise_reverse]; exact hpairL
  have hhead : ∀ x ∈ l.reverse.head?, 2 ≤ x := by
    intro x hx; apply hall; rw [← List.mem_reverse]; exact List.mem_of_mem_head? hx
  -- 1 - r² = r  (via φ⁻¹ = φ − 1)
  have hinv_eq : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]; linarith [Real.goldenRatio_add_goldenConj]
  have hrr : Real.goldenRatio⁻¹ + (Real.goldenRatio⁻¹) ^ 2 = 1 := by
    rw [hinv_eq]; linear_combination Real.goldenRatio_sq
  have h1r2 : 1 - (Real.goldenRatio⁻¹) ^ 2 = Real.goldenRatio⁻¹ := by linarith
  have hrne : Real.goldenRatio⁻¹ ≠ 0 := inv_ne_zero hφne
  have hfinal : (Real.goldenRatio⁻¹) ^ 2 / (1 - (Real.goldenRatio⁻¹) ^ 2) = 1 / Real.goldenRatio := by
    rw [h1r2, sq, mul_div_assoc, div_self hrne, mul_one, inv_eq_one_div]
  have hsumrev : (l.map (fun i => (Real.goldenRatio⁻¹) ^ i)).sum
      = (l.reverse.map (fun i => (Real.goldenRatio⁻¹) ^ i)).sum := by
    rw [List.map_reverse, List.sum_reverse]
  rw [AxisWord.betaMinusReal_eq_sum, ← List.sum_toFinset _ hnodup]
  calc |∑ i ∈ l.toFinset, Real.goldenConj ^ i|
      ≤ ∑ i ∈ l.toFinset, |Real.goldenConj ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ l.toFinset, (Real.goldenRatio⁻¹) ^ i := by
        apply Finset.sum_congr rfl; intro i _; rw [abs_pow, abs_goldenConj]
    _ = (l.map (fun i => (Real.goldenRatio⁻¹) ^ i)).sum := List.sum_toFinset _ hnodup
    _ = (l.reverse.map (fun i => (Real.goldenRatio⁻¹) ^ i)).sum := hsumrev
    _ ≤ (Real.goldenRatio⁻¹) ^ 2 / (1 - (Real.goldenRatio⁻¹) ^ 2) :=
        geomBound hr0 hr1 hr2 l.reverse 2 hrev hhead
    _ = 1 / Real.goldenRatio := hfinal

/-- **定理 6.25(亏空三值),无条件**:`deficitInt v w ∈ {−1,0,1}`。
`|k| = |μ(v)+μ(w)−μ(v+w)| ≤ 3/φ < 2`(φ>3/2)与整性(定理 6.22)相交即得。 -/
theorem deficitTrichotomy_holds : DeficitTrichotomy := by
  intro v w
  have hreal := deficit_real_eq v w
  have hv := abs_betaMinus_le v
  have hw := abs_betaMinus_le w
  have hvw := abs_betaMinus_le (v + w)
  have hφpos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have h3 : 3 * (1 / Real.goldenRatio) < 2 := by
    rw [mul_one_div, div_lt_iff₀ hφpos]
    nlinarith [Real.goldenRatio_sq, Real.goldenRatio_lt_two, hφpos]
  set βv := AxisWord.betaMinusReal (AxisWord.encode v)
  set βw := AxisWord.betaMinusReal (AxisWord.encode w)
  set βvw := AxisWord.betaMinusReal (AxisWord.encode (v + w))
  have htri : |βv + βw - βvw| ≤ |βv| + |βw| + |βvw| := by
    rw [sub_eq_add_neg]
    calc |βv + βw + -βvw| ≤ |βv + βw| + |(-βvw)| := abs_add_le _ _
      _ = |βv + βw| + |βvw| := by rw [abs_neg]
      _ ≤ |βv| + |βw| + |βvw| := by linarith [abs_add_le βv βw]
  have habs : |(deficitInt v w : ℝ)| < 2 := by
    rw [hreal]
    have : |βv + βw - βvw| ≤ 3 * (1 / Real.goldenRatio) := by
      have := htri; nlinarith [hv, hw, hvw, htri]
    linarith [this, h3]
  have hup : deficitInt v w < 2 := by
    have := (abs_lt.mp habs).2; exact_mod_cast this
  have hlo : -2 < deficitInt v w := by
    have := (abs_lt.mp habs).1; exact_mod_cast this
  omega

end UnifiedTheory
