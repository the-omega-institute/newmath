import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.NarayanaCowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

def narayanaCow : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => narayanaCow (n + 2) + narayanaCow n

def narayanaCowHist (n : Nat) : BHist :=
  natToUnary (narayanaCow n)

theorem narayanaCow_zero :
    narayanaCow 0 = 1 := by
  rfl

theorem narayanaCow_one :
    narayanaCow 1 = 1 := by
  rfl

theorem narayanaCow_two :
    narayanaCow 2 = 1 := by
  rfl

theorem narayanaCow_recurrence (n : Nat) :
    narayanaCow (n + 3) = narayanaCow (n + 2) + narayanaCow n := by
  rfl

theorem narayanaCow_three :
    narayanaCow 3 = 2 := by
  rfl

theorem narayanaCow_four :
    narayanaCow 4 = 3 := by
  rfl

theorem narayanaCow_five :
    narayanaCow 5 = 4 := by
  rfl

theorem narayanaCow_step_le (n : Nat) :
    narayanaCow (n + 2) <= narayanaCow (n + 3) := by
  rw [narayanaCow_recurrence n]
  exact Nat.le_add_right (narayanaCow (n + 2)) (narayanaCow n)

theorem narayanaCowHist_unary (n : Nat) :
    UnaryHistory (narayanaCowHist n) := by
  unfold narayanaCowHist
  exact natToUnary_unary _

theorem NarayanaCowUp_constructive_export :
    narayanaCow 0 = 1 ∧
      narayanaCow 1 = 1 ∧
        narayanaCow 2 = 1 ∧
          (∀ n : Nat,
            narayanaCow (n + 3) = narayanaCow (n + 2) + narayanaCow n) ∧
            (∀ n : Nat, narayanaCow (n + 2) <= narayanaCow (n + 3)) := by
  constructor
  · exact narayanaCow_zero
  · constructor
    · exact narayanaCow_one
    · constructor
      · exact narayanaCow_two
      · constructor
        · intro n
          exact narayanaCow_recurrence n
        · intro n
          exact narayanaCow_step_le n

end BEDC.Derived.NarayanaCowUp
