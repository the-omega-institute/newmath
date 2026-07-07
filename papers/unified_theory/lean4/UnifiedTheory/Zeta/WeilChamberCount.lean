import Mathlib

namespace UnifiedTheory

/-- `< N` 的素数幂集合(有限 Weil 素边的存活频率索引)。 -/
def ppChamber (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun q : ℕ => IsPrimePow q)

/-- 单调:窗口变宽只增不减。 -/
theorem ppChamber_mono {M N : ℕ} (hMN : M ≤ N) : ppChamber M ⊆ ppChamber N := by
  intro q hq
  rw [ppChamber] at hq ⊢
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp hq).1) hMN),
      (Finset.mem_filter.mp hq).2⟩

/-- 计数逐步:`N+1` 处仅当 `N` 是素数幂才 +1。 -/
theorem ppChamber_card_succ (N : ℕ) :
    (ppChamber (N + 1)).card = (ppChamber N).card + (if IsPrimePow N then 1 else 0) := by
  classical
  have hnot : N ∉ (Finset.range N).filter (fun q : ℕ => IsPrimePow q) := by
    intro hN
    exact Nat.lt_irrefl N (Finset.mem_range.mp (Finset.mem_of_mem_filter N hN))
  rw [ppChamber, Finset.range_add_one, Finset.filter_insert]
  by_cases hN : IsPrimePow N
  · rw [if_pos hN, if_pos hN, Finset.card_insert_of_notMem hnot]
    rfl
  · rw [if_neg hN, if_neg hN]
    rfl

/-- 精确边界:`ppChamber` 在 `N` 处增长 ⟺ `N` 是素数幂。 -/
theorem ppChamber_gains_iff (N : ℕ) :
    ppChamber (N + 1) ≠ ppChamber N ↔ IsPrimePow N := by
  classical
  have hnot : N ∉ (Finset.range N).filter (fun q : ℕ => IsPrimePow q) := by
    intro hN
    exact Nat.lt_irrefl N (Finset.mem_range.mp (Finset.mem_of_mem_filter N hN))
  rw [ppChamber, Finset.range_add_one, Finset.filter_insert]
  by_cases hN : IsPrimePow N
  · rw [if_pos hN]
    constructor
    · intro _h
      exact hN
    · intro _h
      exact Finset.insert_ne_self.mpr hnot
  · rw [if_neg hN]
    constructor
    · intro h
      exact False.elim (h rfl)
    · intro h
      exact False.elim (hN h)

end UnifiedTheory
