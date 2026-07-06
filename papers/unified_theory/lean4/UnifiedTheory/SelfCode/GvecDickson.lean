import UnifiedTheory.SelfCode.GodelVec
import Mathlib.Order.WellQuasiOrder

namespace UnifiedTheory.SelfCode

open UnifiedTheory

/-- Dickson: every infinite sequence in `Fin k → ℕ` has a coordinatewise increasing pair. -/
theorem finiteAxis_dickson (k : ℕ) (x : ℕ → Fin k → ℕ) :
    ∃ i j : ℕ, i < j ∧ ∀ t : Fin k, x i t ≤ x j t := by
  have h : WellQuasiOrdered (fun a b : (Fin k → ℕ) => a ≤ b) := wellQuasiOrdered_le
  obtain ⟨i, j, hij, hle⟩ := h x
  exact ⟨i, j, hij, fun t => hle t⟩

/-- Fixed-axis Gödel vectors have no infinite divisibility antichain. -/
theorem Gvec_fixedAxis_dividing_pair (k : ℕ) (p : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (x : ℕ → Fin k → ℕ) :
    ∃ i j : ℕ, i < j ∧ Gvec p (x i) ∣ Gvec p (x j) := by
  obtain ⟨i, j, hij, hxy⟩ := finiteAxis_dickson k x
  exact ⟨i, j, hij, (Gvec_dvd_iff p hp hinj (x i) (x j)).2 hxy⟩

end UnifiedTheory.SelfCode
