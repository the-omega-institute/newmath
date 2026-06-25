import BEDC.Derived.FactorialUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.DerangementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.RationalUp

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp

abbrev derangementNumber : Nat -> Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangementNumber (n + 1) + derangementNumber n)

abbrev alternatingSignIntegerUp : Nat -> IntegerUp
  | 0 => intOne
  | n + 1 => IntNeg (alternatingSignIntegerUp n)

abbrev alternatingSignInt : Nat -> Int
  | 0 => 1
  | n + 1 => -alternatingSignInt n

abbrev derangementSignedRecurrenceNumber : Nat -> Int
  | 0 => 1
  | n + 1 => ((n + 1 : Nat) : Int) * derangementSignedRecurrenceNumber n -
      alternatingSignInt n

def derangementInteger : Nat -> IntegerUp :=
  fun n => intOfNat (natToUnary (derangementNumber n)) (natToUnary_unary _)

def derangementAlternatingStep (n : Nat) : IntegerUp :=
  IntAdd
    (IntMul
      (intOfNat (natToUnary n) (natToUnary_unary _))
      (derangementInteger (n - 1)))
    (alternatingSignIntegerUp n)

theorem derangementNumber_zero :
    derangementNumber 0 = 1 := by
  rfl

theorem derangementNumber_one :
    derangementNumber 1 = 0 := by
  rfl

theorem derangementNumber_two :
    derangementNumber 2 = 1 := by
  rfl

theorem derangementNumber_three :
    derangementNumber 3 = 2 := by
  rfl

theorem derangementNumber_four :
    derangementNumber 4 = 9 := by
  rfl

theorem derangementNumber_recurrence (n : Nat) :
    derangementNumber (n + 2) =
      (n + 1) * (derangementNumber (n + 1) + derangementNumber n) := by
  rfl

theorem derangementNumber_succ_succ_recurrence (n : Nat) :
    derangementNumber (Nat.succ (Nat.succ n)) =
      Nat.succ n * (derangementNumber (Nat.succ n) + derangementNumber n) := by
  rfl

theorem derangementSignedRecurrenceNumber_zero :
    derangementSignedRecurrenceNumber 0 = 1 := by
  rfl

theorem derangementSignedRecurrenceNumber_succ (n : Nat) :
    derangementSignedRecurrenceNumber (n + 1) =
      ((n + 1 : Nat) : Int) * derangementSignedRecurrenceNumber n -
        alternatingSignInt n := by
  rfl

theorem derangementSignedRecurrenceNumber_succ_plus (n : Nat) :
    derangementSignedRecurrenceNumber (n + 1) =
      ((n + 1 : Nat) : Int) * derangementSignedRecurrenceNumber n +
        alternatingSignInt (n + 1) := by
  rfl

theorem derangementSignedRecurrenceNumber_two :
    derangementSignedRecurrenceNumber 2 = 1 := by
  rfl

theorem derangementSignedRecurrenceNumber_three :
    derangementSignedRecurrenceNumber 3 = 2 := by
  rfl

theorem derangementSignedRecurrenceNumber_four :
    derangementSignedRecurrenceNumber 4 = 9 := by
  rfl

private theorem int_neg_neg (x : IntegerUp) :
    IntEq (IntNeg (IntNeg x)) x :=
  BEDC.Algebra.Rel.IntegerUp_neg_neg x

theorem alternatingSignIntegerUp_zero :
    IntEq (alternatingSignIntegerUp 0) intOne := by
  exact IntEq_refl intOne

theorem alternatingSignIntegerUp_succ (n : Nat) :
    IntEq (alternatingSignIntegerUp (Nat.succ n))
      (IntNeg (alternatingSignIntegerUp n)) := by
  exact IntEq_refl (IntNeg (alternatingSignIntegerUp n))

theorem alternatingSignIntegerUp_two_step (n : Nat) :
    IntEq (alternatingSignIntegerUp (n + 2)) (alternatingSignIntegerUp n) := by
  cases n with
  | zero =>
      change IntEq (IntNeg (IntNeg intOne)) intOne
      exact int_neg_neg intOne
  | succ n =>
      change IntEq
        (IntNeg (IntNeg (alternatingSignIntegerUp (Nat.succ n))))
        (alternatingSignIntegerUp (Nat.succ n))
      exact int_neg_neg (alternatingSignIntegerUp (Nat.succ n))

theorem derangementInteger_zero :
    IntEq (derangementInteger 0) intOne := by
  exact IntEq_refl intOne

theorem derangementInteger_one :
    IntEq (derangementInteger 1) intZero := by
  exact IntEq_refl intZero

theorem derangementInteger_two :
    IntEq (derangementInteger 2) intOne := by
  exact IntEq_refl intOne

theorem derangementInteger_three :
    IntEq (derangementInteger 3)
      (intOfNat (natToUnary 2) (natToUnary_unary _)) := by
  exact IntEq_refl (intOfNat (natToUnary 2) (natToUnary_unary _))

theorem derangementInteger_four :
    IntEq (derangementInteger 4)
      (intOfNat (natToUnary 9) (natToUnary_unary _)) := by
  exact IntEq_refl (intOfNat (natToUnary 9) (natToUnary_unary _))

theorem derangementNumber_sum_identity_at_four :
    derangementNumber 4 =
      3 * derangementNumber 3 + 3 * derangementNumber 2 := by
  rfl

theorem derangementNumber_signed_recurrence_at_four :
    ((derangementNumber 4 : Nat) : Int) =
      ((4 : Nat) : Int) * ((derangementNumber 3 : Nat) : Int) +
        alternatingSignInt 4 := by
  rfl

theorem derangementNumber_agrees_with_signed_recurrence_at_four :
    ((derangementNumber 4 : Nat) : Int) = derangementSignedRecurrenceNumber 4 := by
  rfl

theorem DerangementUp_constructive_export :
    derangementNumber 0 = 1 ∧
      derangementNumber 1 = 0 ∧
      derangementNumber 2 = 1 ∧
      derangementNumber 3 = 2 ∧
      derangementNumber 4 = 9 ∧
      (∀ n : Nat,
        derangementNumber (n + 2) =
          (n + 1) * (derangementNumber (n + 1) + derangementNumber n)) := by
  constructor
  · exact derangementNumber_zero
  · constructor
    · exact derangementNumber_one
    · constructor
      · exact derangementNumber_two
      · constructor
        · exact derangementNumber_three
        · constructor
          · exact derangementNumber_four
          · intro n
            exact derangementNumber_recurrence n

end BEDC.Derived.DerangementUp
