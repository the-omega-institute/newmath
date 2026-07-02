import BEDC.Derived.DerangementUp
import Mathlib.Combinatorics.Derangements.Finite

namespace BedcMathlibBridge.Constructive.Derangement

private def mathlibNumDerangementsProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, numDerangements n = numDerangements n :=
    fun _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibNumDerangementsProvenanceAnchor
  BEDC.Derived.DerangementUp.derangementNumber n

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_one : toNat 1 = 0 := by
  rfl

theorem toNat_add_two (n : Nat) :
    toNat (n + 2) = (n + 1) * (toNat (n + 1) + toNat n) := by
  rfl

private theorem toNat_pair_eq_numDerangements (n : Nat) :
    toNat n = numDerangements n ∧
      toNat (n + 1) = numDerangements (n + 1) := by
  induction n with
  | zero =>
      exact ⟨toNat_zero, toNat_one⟩
  | succ n ih =>
      refine ⟨ih.right, ?_⟩
      calc
        toNat (n + 2) = (n + 1) * (toNat (n + 1) + toNat n) :=
          toNat_add_two n
        _ = (n + 1) * (numDerangements (n + 1) + numDerangements n) := by
          rw [ih.left, ih.right]
        _ = (n + 1) * (numDerangements n + numDerangements (n + 1)) := by
          rw [Nat.add_comm (numDerangements (n + 1)) (numDerangements n)]
        _ = numDerangements (n + 2) := (numDerangements_add_two n).symm

theorem toNat_eq_numDerangements (n : Nat) :
    toNat n = numDerangements n :=
  (toNat_pair_eq_numDerangements n).left

end BedcMathlibBridge.Constructive.Derangement
