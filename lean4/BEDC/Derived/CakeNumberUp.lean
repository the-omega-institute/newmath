import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.CakeNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

def triangularNumber : Nat -> Nat
  | 0 => 0
  | Nat.succ n => triangularNumber n + Nat.succ n

def cakeNumber : Nat -> Nat
  | 0 => 1
  | Nat.succ n => cakeNumber n + Nat.succ n

def cakeNumberHist (n : Nat) : BHist :=
  natToUnary (cakeNumber n)

theorem triangularNumber_zero :
    triangularNumber 0 = 0 := by
  rfl

theorem triangularNumber_succ (n : Nat) :
    triangularNumber (Nat.succ n) = triangularNumber n + Nat.succ n := by
  rfl

theorem cakeNumber_zero :
    cakeNumber 0 = 1 := by
  rfl

theorem cakeNumber_succ (n : Nat) :
    cakeNumber (Nat.succ n) = cakeNumber n + Nat.succ n := by
  rfl

theorem cakeNumber_eq_triangular_add_one (n : Nat) :
    cakeNumber n = triangularNumber n + 1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change cakeNumber n + Nat.succ n =
        (triangularNumber n + Nat.succ n) + 1
      rw [ih]
      calc
        triangularNumber n + 1 + Nat.succ n =
            triangularNumber n + (1 + Nat.succ n) := by
              rw [Nat.add_assoc]
        _ = triangularNumber n + (Nat.succ n + 1) := by
              rw [Nat.add_comm 1 (Nat.succ n)]
        _ = triangularNumber n + Nat.succ n + 1 := by
              rw [Nat.add_assoc]

theorem cakeNumber_one :
    cakeNumber 1 = 2 := by
  rfl

theorem cakeNumber_two :
    cakeNumber 2 = 4 := by
  rfl

theorem cakeNumber_three :
    cakeNumber 3 = 7 := by
  rfl

theorem cakeNumber_four :
    cakeNumber 4 = 11 := by
  rfl

theorem cakeNumberHist_unary (n : Nat) :
    UnaryHistory (cakeNumberHist n) := by
  unfold cakeNumberHist
  exact natToUnary_unary _

theorem CakeNumberUp_constructive_export :
    cakeNumber 0 = 1 ∧
      (∀ n : Nat, cakeNumber (Nat.succ n) = cakeNumber n + Nat.succ n) ∧
        (∀ n : Nat, cakeNumber n = triangularNumber n + 1) ∧
          cakeNumber 4 = 11 := by
  constructor
  · exact cakeNumber_zero
  · constructor
    · intro n
      exact cakeNumber_succ n
    · constructor
      · intro n
        exact cakeNumber_eq_triangular_add_one n
      · exact cakeNumber_four

end BEDC.Derived.CakeNumberUp
