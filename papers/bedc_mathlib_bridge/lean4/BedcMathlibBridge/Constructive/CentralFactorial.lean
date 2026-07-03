import BedcMathlibBridge.Export.StirlingSecond
import BEDC.Derived.CentralFactorialUp

/-!
Central factorial strip correspondence.

The exported surface is deliberately narrow: it records only the diagonal,
above-diagonal, and seed-row strips where the BEDC second-kind central
factorial table is already proved to agree with BEDC Stirling second-kind
numbers, then transports those cells to mathlib `Nat.stirlingSecond`.
-/

namespace BedcMathlibBridge.Constructive.CentralFactorial

private def mathlibStirlingSecondProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.stirlingSecond n k = Nat.stirlingSecond n k :=
    fun _ _ => rfl
  ()

def toNat (n k : Nat) : Nat :=
  let _ := mathlibStirlingSecondProvenanceAnchor
  BEDC.Derived.CentralFactorialUp.centralFactorialSecond n k

theorem toNat_apply (n k : Nat) :
    toNat n k =
      BEDC.Derived.CentralFactorialUp.centralFactorialSecond n k := by
  rfl

theorem diagonal_eq_nat_stirlingSecond (n : Nat) :
    toNat n n = Nat.stirlingSecond n n := by
  rw [toNat_apply]
  rw [BEDC.Derived.CentralFactorialUp.centralFactorialSecond_self_matches_stirlingSecond_self]
  exact BedcMathlibBridge.Export.StirlingSecond.stirlingSecond_eq_nat_stirlingSecond n n

theorem above_diagonal_eq_nat_stirlingSecond (n extra : Nat) :
    toNat n (Nat.succ (n + extra)) =
      Nat.stirlingSecond n (Nat.succ (n + extra)) := by
  rw [toNat_apply]
  rw [BEDC.Derived.CentralFactorialUp.centralFactorialSecond_above_matches_stirlingSecond_above]
  exact
    BedcMathlibBridge.Export.StirlingSecond.stirlingSecond_eq_nat_stirlingSecond n
      (Nat.succ (n + extra))

theorem zero_row_eq_nat_stirlingSecond (k : Nat) :
    toNat 0 k = Nat.stirlingSecond 0 k := by
  rw [toNat_apply]
  rw [BEDC.Derived.CentralFactorialUp.centralFactorialSecond_zero_row_stirling]
  exact BedcMathlibBridge.Export.StirlingSecond.stirlingSecond_eq_nat_stirlingSecond 0 k

theorem one_row_eq_nat_stirlingSecond (k : Nat) :
    toNat 1 k = Nat.stirlingSecond 1 k := by
  rw [toNat_apply]
  rw [BEDC.Derived.CentralFactorialUp.centralFactorialSecond_one_row_stirling]
  exact BedcMathlibBridge.Export.StirlingSecond.stirlingSecond_eq_nat_stirlingSecond 1 k

end BedcMathlibBridge.Constructive.CentralFactorial
