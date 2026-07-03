import BEDC.Derived.LucasTheoremUp
import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.Binomial

open BEDC.Derived.LucasTheoremUp

private theorem bedcChoose_zero_zero :
    bedcChooseNat 0 0 = 1 := by
  unfold bedcChooseNat BEDC.Derived.FactorialUp.natChooseFn
  repeat rw [BEDC.Derived.IntUp.natToUnary_length]
  rfl

private theorem bedcChoose_zero_succ (k : Nat) :
    bedcChooseNat 0 (Nat.succ k) = 0 := by
  unfold bedcChooseNat BEDC.Derived.FactorialUp.natChooseFn
  repeat rw [BEDC.Derived.IntUp.natToUnary_length]
  rfl

private theorem bedcChoose_succ_zero (n : Nat) :
    bedcChooseNat (Nat.succ n) 0 = 1 := by
  unfold bedcChooseNat BEDC.Derived.FactorialUp.natChooseFn
  repeat rw [BEDC.Derived.IntUp.natToUnary_length]
  rfl

theorem bedcChoose_eq_nat_choose (n k : Nat) :
    bedcChooseNat n k = Nat.choose n k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero =>
          exact bedcChoose_zero_zero
      | succ k =>
          rw [bedcChoose_zero_succ, Nat.choose_zero_succ]
  | succ n ih =>
      cases k with
      | zero =>
          rw [bedcChoose_succ_zero, Nat.choose_zero_right]
      | succ k =>
          calc
            bedcChooseNat (Nat.succ n) (Nat.succ k) =
                bedcChooseNat n k + bedcChooseNat n (Nat.succ k) :=
              bedcChooseNat_pascal n k
            _ = Nat.choose n k + Nat.choose n (Nat.succ k) := by
              rw [ih k, ih (Nat.succ k)]
            _ = Nat.choose (Nat.succ n) (Nat.succ k) :=
              (Nat.choose_succ_succ n k).symm

end BedcMathlibBridge.Constructive.Binomial
