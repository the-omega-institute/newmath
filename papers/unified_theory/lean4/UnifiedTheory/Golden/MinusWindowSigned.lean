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

end UnifiedTheory
