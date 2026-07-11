import BEDC.Derived.CakeNumberUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Cake number structural correspondence.

`BEDC.Derived.CakeNumberUp.cakeNumber n` is the BEDC recurrence
`1, 2, 4, 7, ...`, with the checked identity against the local BEDC triangular
recurrence plus one. The bridge target is the binomial expression

  `Nat.choose (n + 1) 2 + 1`.

The triangular-to-binomial step is proved here by Pascal induction, using only
zero-axiom `Nat.choose` facts.
-/

namespace BedcMathlibBridge.Constructive.CakeNumber

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

private theorem choose_one_right' (n : Nat) : Nat.choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.choose_succ_succ n 0, Nat.choose_zero_right, ih, Nat.add_comm]

private theorem triangularNumber_eq_nat_choose (n : Nat) :
    BEDC.Derived.CakeNumberUp.triangularNumber n = Nat.choose (n + 1) 2 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        BEDC.Derived.CakeNumberUp.triangularNumber (Nat.succ n)
            = BEDC.Derived.CakeNumberUp.triangularNumber n + Nat.succ n :=
              BEDC.Derived.CakeNumberUp.triangularNumber_succ n
        _ = Nat.choose (n + 1) 2 + Nat.succ n := by
              rw [ih]
        _ = Nat.succ n + Nat.choose (n + 1) 2 := Nat.add_comm _ _
        _ = Nat.choose (Nat.succ n + 1) 2 := by
              rw [Nat.choose_succ_succ (n + 1) 1, choose_one_right']

def toNat (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.CakeNumberUp.cakeNumber n

theorem toNat_eq_cakeNumber (n : Nat) :
    toNat n = BEDC.Derived.CakeNumberUp.cakeNumber n :=
  rfl

theorem toNat_zero : toNat 0 = 1 := by
  rfl

theorem toNat_one : toNat 1 = 2 := by
  rfl

theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = toNat n + Nat.succ n := by
  change
    BEDC.Derived.CakeNumberUp.cakeNumber (Nat.succ n) =
      BEDC.Derived.CakeNumberUp.cakeNumber n + Nat.succ n
  exact BEDC.Derived.CakeNumberUp.cakeNumber_succ n

theorem toNat_eq_nat_choose_add_one (n : Nat) :
    toNat n = Nat.choose (n + 1) 2 + 1 := by
  calc
    toNat n = BEDC.Derived.CakeNumberUp.cakeNumber n := rfl
    _ = BEDC.Derived.CakeNumberUp.triangularNumber n + 1 :=
      BEDC.Derived.CakeNumberUp.cakeNumber_eq_triangular_add_one n
    _ = Nat.choose (n + 1) 2 + 1 := by
      rw [triangularNumber_eq_nat_choose n]

end BedcMathlibBridge.Constructive.CakeNumber
