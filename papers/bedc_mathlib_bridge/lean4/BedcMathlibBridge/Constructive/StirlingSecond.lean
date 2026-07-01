import BEDC.Derived.StirlingUp
import Mathlib.Combinatorics.Enumerative.Stirling

namespace BedcMathlibBridge.Constructive.StirlingSecond

private def mathlibStirlingSecondProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.stirlingSecond n k = Nat.stirlingSecond n k :=
    fun _ _ => rfl
  ()

def toNat (n k : Nat) : Nat :=
  let _ := mathlibStirlingSecondProvenanceAnchor
  BEDC.Derived.StirlingUp.stirlingSecond n k

theorem toNat_zero_zero : toNat 0 0 = 1 := by
  rfl

theorem toNat_zero_succ (k : Nat) : toNat 0 (Nat.succ k) = 0 := by
  rfl

theorem toNat_succ_zero (n : Nat) : toNat (Nat.succ n) 0 = 0 := by
  rfl

theorem toNat_succ_succ (n k : Nat) :
    toNat (Nat.succ n) (Nat.succ k) =
      Nat.succ k * toNat n (Nat.succ k) + toNat n k := by
  rfl

theorem toNat_eq_nat_stirlingSecond (n k : Nat) :
    toNat n k = Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero =>
          rfl
      | succ k =>
          rw [toNat_zero_succ, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
      cases k with
      | zero =>
          rw [toNat_succ_zero, Nat.stirlingSecond_succ_zero]
      | succ k =>
          calc
            toNat (Nat.succ n) (Nat.succ k) =
                Nat.succ k * toNat n (Nat.succ k) + toNat n k :=
              toNat_succ_succ n k
            _ = Nat.succ k * Nat.stirlingSecond n (Nat.succ k) +
                Nat.stirlingSecond n k := by
              rw [ih (Nat.succ k), ih k]
            _ = Nat.stirlingSecond (Nat.succ n) (Nat.succ k) :=
              (Nat.stirlingSecond_succ_succ n k).symm

end BedcMathlibBridge.Constructive.StirlingSecond
