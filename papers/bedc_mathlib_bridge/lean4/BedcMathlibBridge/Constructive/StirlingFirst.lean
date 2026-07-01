import BEDC.Derived.StirlingFirstUp
import Mathlib.Combinatorics.Enumerative.Stirling

namespace BedcMathlibBridge.Constructive.StirlingFirst

abbrev toNat (n k : Nat) : Nat :=
  BEDC.Derived.StirlingFirstUp.stirlingFirst n k

theorem toNat_zero_zero : toNat 0 0 = 1 := by
  rfl

theorem toNat_zero_succ (k : Nat) : toNat 0 (Nat.succ k) = 0 := by
  rfl

theorem toNat_succ_zero (n : Nat) : toNat (Nat.succ n) 0 = 0 := by
  rfl

theorem toNat_succ_succ (n k : Nat) :
    toNat (Nat.succ n) (Nat.succ k) =
      n * toNat n (Nat.succ k) + toNat n k := by
  rfl

theorem toNat_eq_nat_stirlingFirst (n k : Nat) :
    toNat n k = Nat.stirlingFirst n k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero =>
          rfl
      | succ k =>
          rw [toNat_zero_succ, Nat.stirlingFirst_zero_succ]
  | succ n ih =>
      cases k with
      | zero =>
          rw [toNat_succ_zero, Nat.stirlingFirst_succ_zero]
      | succ k =>
          calc
            toNat (Nat.succ n) (Nat.succ k) =
                n * toNat n (Nat.succ k) + toNat n k :=
              toNat_succ_succ n k
            _ = n * Nat.stirlingFirst n (Nat.succ k) +
                Nat.stirlingFirst n k := by
              rw [ih (Nat.succ k), ih k]
            _ = Nat.stirlingFirst (Nat.succ n) (Nat.succ k) :=
              (Nat.stirlingFirst_succ_succ n k).symm

end BedcMathlibBridge.Constructive.StirlingFirst
