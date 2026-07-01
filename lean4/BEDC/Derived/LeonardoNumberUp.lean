import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.LeonardoNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

def leonardoNumber : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => leonardoNumber (n + 1) + leonardoNumber n + 1

def shiftedLeonardo (n : Nat) : Nat :=
  leonardoNumber n + 1

def leonardoHist (n : Nat) : BHist :=
  natToUnary (leonardoNumber n)

theorem leonardo_zero :
    leonardoNumber 0 = 1 := by
  rfl

theorem leonardo_one :
    leonardoNumber 1 = 1 := by
  rfl

theorem leonardo_recurrence (n : Nat) :
    leonardoNumber (n + 2) =
      leonardoNumber (n + 1) + leonardoNumber n + 1 := by
  rfl

theorem leonardo_two :
    leonardoNumber 2 = 3 := by
  rfl

theorem leonardo_three :
    leonardoNumber 3 = 5 := by
  rfl

theorem leonardo_four :
    leonardoNumber 4 = 9 := by
  rfl

theorem shiftedLeonardo_zero :
    shiftedLeonardo 0 = 2 := by
  rfl

theorem shiftedLeonardo_one :
    shiftedLeonardo 1 = 2 := by
  rfl

theorem shiftedLeonardo_recurrence (n : Nat) :
    shiftedLeonardo (n + 2) =
      shiftedLeonardo (n + 1) + shiftedLeonardo n := by
  unfold shiftedLeonardo
  rw [leonardo_recurrence n]
  calc
    leonardoNumber (n + 1) + leonardoNumber n + 1 + 1 =
        leonardoNumber (n + 1) + (leonardoNumber n + 1) + 1 := by
          rw [Nat.add_assoc (leonardoNumber (n + 1)) (leonardoNumber n) 1]
    _ = leonardoNumber (n + 1) + 1 + (leonardoNumber n + 1) := by
          rw [Nat.add_assoc]
          rw [Nat.add_comm (leonardoNumber n + 1) 1]
          rw [← Nat.add_assoc]

theorem leonardoHist_unary (n : Nat) :
    UnaryHistory (leonardoHist n) := by
  unfold leonardoHist
  exact natToUnary_unary _

theorem LeonardoNumberUp_constructive_export :
    leonardoNumber 0 = 1 ∧
      leonardoNumber 1 = 1 ∧
        (∀ n : Nat,
          leonardoNumber (n + 2) =
            leonardoNumber (n + 1) + leonardoNumber n + 1) ∧
          (∀ n : Nat,
            shiftedLeonardo (n + 2) =
              shiftedLeonardo (n + 1) + shiftedLeonardo n) ∧
            leonardoNumber 4 = 9 := by
  constructor
  · exact leonardo_zero
  · constructor
    · exact leonardo_one
    · constructor
      · intro n
        exact leonardo_recurrence n
      · constructor
        · intro n
          exact shiftedLeonardo_recurrence n
        · exact leonardo_four

end BEDC.Derived.LeonardoNumberUp
