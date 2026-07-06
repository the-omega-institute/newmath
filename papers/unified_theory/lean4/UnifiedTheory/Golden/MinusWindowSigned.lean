import UnifiedTheory.Golden.MinusWindow

namespace UnifiedTheory

/-- **严格几何界**:有限链严格小于无穷和上确界,`geomBound` 的 `<` 版,
供 MinusWindow 符号下界用。 -/
theorem geomBoundStrict {r : ℝ} (hr0pos : 0 < r) (hr1 : r ≤ 1) (hr2 : r ^ 2 < 1) :
    ∀ (m : List ℕ) (b : ℕ), m.IsChain (fun a c => a + 2 ≤ c) →
      (∀ x ∈ m.head?, b ≤ x) →
      (m.map (fun i => r ^ i)).sum < r ^ b / (1 - r ^ 2) := by
  have hr0 : 0 ≤ r := le_of_lt hr0pos
  have hden : 0 < 1 - r ^ 2 := by linarith
  intro m
  induction m with
  | nil =>
      intro b _ _
      simp only [List.map_nil, List.sum_nil]
      exact div_pos (pow_pos hr0pos b) hden
  | cons a m' ih =>
      intro b _ hhead
      have hba : b ≤ a := hhead a (by simp)
      rw [List.isChain_cons] at *
      rename_i hchain
      obtain ⟨hrel, hchain'⟩ := hchain
      have hm' : (m'.map (fun i => r ^ i)).sum < r ^ (a + 2) / (1 - r ^ 2) :=
        ih (a + 2) hchain' hrel
      have hpow : r ^ (a + 2) = r ^ a * r ^ 2 := by rw [pow_add]
      have hra : r ^ a ≤ r ^ b := pow_le_pow_of_le_one hr0 hr1 hba
      simp only [List.map_cons, List.sum_cons]
      have hkey : r ^ a + r ^ (a + 2) / (1 - r ^ 2) = r ^ a / (1 - r ^ 2) := by
        rw [hpow]
        field_simp
        ring
      calc r ^ a + (m'.map (fun i => r ^ i)).sum
          < r ^ a + r ^ (a + 2) / (1 - r ^ 2) := by linarith [hm']
        _ = r ^ a / (1 - r ^ 2) := hkey
        _ ≤ r ^ b / (1 - r ^ 2) := (div_le_div_iff_of_pos_right hden).mpr hra

/-- List 三角:符号几何和的绝对值受同链正几何和控制(`|(-r)^i| = r^i`)。 -/
private theorem abs_signed_le (l : List ℕ) :
    |(l.map (fun i => (-(Real.goldenRatio⁻¹)) ^ i)).sum|
      ≤ (l.map (fun i => (Real.goldenRatio⁻¹) ^ i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      have hpow : |(-(Real.goldenRatio⁻¹)) ^ a| = (Real.goldenRatio⁻¹) ^ a := by
        rw [abs_pow, abs_neg, abs_of_nonneg (le_of_lt (inv_pos.mpr Real.goldenRatio_pos))]
      calc |(-(Real.goldenRatio⁻¹)) ^ a + (l.map (fun i => (-(Real.goldenRatio⁻¹)) ^ i)).sum|
          ≤ |(-(Real.goldenRatio⁻¹)) ^ a| + |(l.map (fun i => (-(Real.goldenRatio⁻¹)) ^ i)).sum| :=
            abs_add_le _ _
        _ ≤ (Real.goldenRatio⁻¹) ^ a + (l.map (fun i => (Real.goldenRatio⁻¹) ^ i)).sum := by
            rw [hpow]; linarith [ih]

/-- **符号几何窗口核心不等式**:合法 Zeckendorf 升序链上 `Σ(-r)^i ∈ (-1/φ², 1/φ)`(`r=φ⁻¹`)。
奇偶拆最小指标 + `geomBoundStrict` 严格尾界。 -/
theorem signedGeom_window (m : List ℕ)
    (hchain : m.IsChain (fun a c => a + 2 ≤ c)) (hhead : ∀ x ∈ m.head?, 2 ≤ x) :
    -(1 / Real.goldenRatio ^ 2) < (m.map (fun i => (-(Real.goldenRatio⁻¹)) ^ i)).sum
      ∧ (m.map (fun i => (-(Real.goldenRatio⁻¹)) ^ i)).sum < 1 / Real.goldenRatio := by
  set r : ℝ := Real.goldenRatio⁻¹ with hrdef
  have hφpos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hr0pos : 0 < r := inv_pos.mpr hφpos
  have hr0 : 0 ≤ r := le_of_lt hr0pos
  have hrφ : r * Real.goldenRatio = 1 := inv_mul_cancel₀ (ne_of_gt hφpos)
  have hφ1 : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hinv_eq : r = Real.goldenRatio - 1 := by
    rw [hrdef, Real.inv_goldenRatio]; linarith [Real.goldenRatio_add_goldenConj]
  have hrr : r + r ^ 2 = 1 := by rw [hinv_eq]; linear_combination Real.goldenRatio_sq
  have h1r2 : 1 - r ^ 2 = r := by linarith
  have hr1lt : r < 1 := by nlinarith [hrr, hr0pos]
  have hr1 : r ≤ 1 := le_of_lt hr1lt
  have hr2 : r ^ 2 < 1 := by linarith [hrr, hr0pos]
  have h1pr : 1 + r = Real.goldenRatio := by rw [hinv_eq]; ring
  have hr2_eq : r ^ 2 = 1 / Real.goldenRatio ^ 2 := by rw [hrdef, inv_pow, one_div]
  have h1φ : 1 / Real.goldenRatio = r := by rw [hrdef, one_div]
  match m, hchain, hhead with
  | [], _, _ =>
      refine ⟨?_, ?_⟩ <;> simp only [List.map_nil, List.sum_nil]
      · have : (0 : ℝ) < 1 / Real.goldenRatio ^ 2 := by positivity
        linarith
      · positivity
  | a :: rest, hchain, hhead =>
      have ha2 : 2 ≤ a := hhead a (by simp)
      rw [List.isChain_cons] at hchain
      obtain ⟨hrel, hrest⟩ := hchain
      have hAr : (rest.map (fun i => r ^ i)).sum < r ^ (a + 2) / (1 - r ^ 2) :=
        geomBoundStrict hr0pos hr1 hr2 rest (a + 2) hrest hrel
      rw [h1r2] at hAr
      have hdiv : r ^ (a + 2) / r = r ^ (a + 1) := by
        rw [pow_add r (a + 1) 1, pow_one, mul_div_assoc, div_self (ne_of_gt hr0pos), mul_one]
      rw [hdiv] at hAr
      have hSabs := abs_signed_le rest
      rw [← hrdef] at hSabs
      have hSlt : |(rest.map (fun i => (-r) ^ i)).sum| < r ^ (a + 1) :=
        lt_of_le_of_lt hSabs hAr
      obtain ⟨hSlo, hShi⟩ := abs_lt.mp hSlt
      simp only [List.map_cons, List.sum_cons]
      have hra_pos : 0 < r ^ a := pow_pos hr0pos a
      have hpow1 : r ^ (a + 1) = r ^ a * r := by rw [pow_succ]
      rcases Nat.even_or_odd a with he | ho
      · -- a even: (-r)^a = r^a
        have hpa : (-r) ^ a = r ^ a := he.neg_pow r
        have hra_le : r ^ a ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1 ha2
        have hr2φ : r ^ 2 * Real.goldenRatio = r := by rw [sq, mul_assoc, hrφ, mul_one]
        refine ⟨?_, ?_⟩ <;> rw [hpa]
        · nlinarith [hSlo, hra_pos, hr1lt, hpow1, hr2_eq]
        · nlinarith [hShi, hra_le, hr2φ, hφpos, hpow1, h1pr, h1φ, hra_pos]
      · -- a odd: (-r)^a = -r^a, and a ≥ 3
        have hpa : (-r) ^ a = -r ^ a := ho.neg_pow r
        have ha3 : 3 ≤ a := by rcases ho with ⟨k, rfl⟩; omega
        have hra_le3 : r ^ a ≤ r ^ 3 := pow_le_pow_of_le_one hr0 hr1 ha3
        have hr3φ : r ^ 3 * Real.goldenRatio = r ^ 2 := by
          rw [pow_succ, mul_assoc, hrφ, mul_one]
        refine ⟨?_, ?_⟩ <;> rw [hpa]
        · nlinarith [hSlo, hra_le3, hr3φ, hr2_eq, hφpos, h1pr, hpow1, hra_pos]
        · nlinarith [hShi, hra_pos, hr1lt, hpow1, h1φ]

end UnifiedTheory
