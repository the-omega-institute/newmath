import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.DerangementUp
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.RencontresNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev derangementNumber : Nat -> Nat :=
  BEDC.Derived.DerangementUp.derangementNumber

def rencontresNumber (n k : Nat) : Nat :=
  C n k * derangementNumber (n - k)

def rencontresNumberHist (n k : Nat) : BHist :=
  natToUnary (rencontresNumber n k)

theorem rencontresNumber_fixed_all (n : Nat) :
    rencontresNumber n n = 1 := by
  unfold rencontresNumber C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_self n]
  rw [Nat.sub_self]
  unfold derangementNumber
  rw [BEDC.Derived.DerangementUp.derangementNumber_zero]

theorem rencontresNumber_fixed_none (n : Nat) :
    rencontresNumber n 0 = derangementNumber n := by
  unfold rencontresNumber C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n]
  rw [Nat.sub_zero]
  rw [Nat.one_mul]

theorem rencontresNumber_above (n : Nat) :
    rencontresNumber n (Nat.succ n) = 0 := by
  unfold rencontresNumber C
  rw [show Nat.succ n = Nat.succ (n + 0) by rw [Nat.add_zero]]
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_above n 0]
  rw [Nat.zero_mul]

theorem rencontresNumber_three_one :
    rencontresNumber 3 1 = 3 := by
  rfl

theorem rencontresNumber_four_two :
    rencontresNumber 4 2 = 6 := by
  rfl

theorem rencontresNumberHist_unary (n k : Nat) :
    UnaryHistory (rencontresNumberHist n k) := by
  unfold rencontresNumberHist
  exact natToUnary_unary _

theorem RencontresNumberUp_constructive_export :
    (∀ n : Nat, rencontresNumber n n = 1) ∧
      (∀ n : Nat, rencontresNumber n 0 = derangementNumber n) ∧
        (∀ n : Nat, rencontresNumber n (Nat.succ n) = 0) ∧
          rencontresNumber 3 1 = 3 ∧ rencontresNumber 4 2 = 6 := by
  constructor
  · intro n
    exact rencontresNumber_fixed_all n
  · constructor
    · intro n
      exact rencontresNumber_fixed_none n
    · constructor
      · intro n
        exact rencontresNumber_above n
      · constructor
        · exact rencontresNumber_three_one
        · exact rencontresNumber_four_two

end BEDC.Derived.RencontresNumberUp
