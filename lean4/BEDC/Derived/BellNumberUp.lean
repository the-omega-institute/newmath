import BEDC.Derived.StirlingUp
import BEDC.Derived.FactorialUp

namespace BEDC.Derived.BellNumberUp

open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.FactorialUp (natChooseFn)
open BEDC.Derived.IntUp (natToUnary natToUnary_length)
open BEDC.Derived.StirlingUp (stirlingSecond)

def bellStirlingPrefix (n : Nat) : Nat -> Nat :=
  BEDC.Derived.StirlingUp.bellPrefix n

def bellNumber (n : Nat) : Nat :=
  bellStirlingPrefix n n

def natChooseCount (n k : Nat) : Nat :=
  bwordLength (natChooseFn (natToUnary n) (natToUnary k))

def bellRecurrencePrefix (B : Nat -> Nat) (n : Nat) : Nat -> Nat
  | 0 => natChooseCount n 0 * B 0
  | Nat.succ k =>
      bellRecurrencePrefix B n k + natChooseCount n (Nat.succ k) * B (Nat.succ k)

def bellRecurrenceSum (n : Nat) : Nat :=
  bellRecurrencePrefix bellNumber n n

def bellRecurrenceFunction : Nat -> Nat -> Nat
  | 0, _ => 1
  | Nat.succ n, k =>
      if k = Nat.succ n then bellRecurrencePrefix (bellRecurrenceFunction n) n n
      else bellRecurrenceFunction n k

def bellNumberByRecurrence (n : Nat) : Nat :=
  bellRecurrenceFunction n n

theorem bellRecurrenceFunction_zero (k : Nat) :
    bellRecurrenceFunction 0 k = 1 := by
  rfl

theorem bellRecurrenceFunction_succ_diagonal (n : Nat) :
    bellRecurrenceFunction (Nat.succ n) (Nat.succ n) =
      bellRecurrencePrefix (bellRecurrenceFunction n) n n := by
  unfold bellRecurrenceFunction
  rw [if_pos rfl]

theorem bellStirlingPrefix_zero (n : Nat) :
    bellStirlingPrefix n 0 = stirlingSecond n 0 := by
  rfl

theorem bellStirlingPrefix_succ (n k : Nat) :
    bellStirlingPrefix n (Nat.succ k) =
      bellStirlingPrefix n k + stirlingSecond n (Nat.succ k) := by
  rfl

theorem bellNumber_sum_definition (n : Nat) :
    bellNumber n = bellStirlingPrefix n n := by
  rfl

theorem bellNumber_matches_StirlingUp (n : Nat) :
    bellNumber n = BEDC.Derived.StirlingUp.bellNumber n := by
  rfl

theorem natChooseCount_zero_zero :
    natChooseCount 0 0 = 1 := by
  rfl

theorem natChooseCount_zero_right (n : Nat) :
    natChooseCount n 0 = 1 := by
  unfold natChooseCount natChooseFn
  rw [natToUnary_length]
  cases n with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem natChooseCount_self (n : Nat) :
    natChooseCount n n = 1 := by
  unfold natChooseCount natChooseFn
  rw [natToUnary_length, natToUnary_length]
  exact BEDC.Derived.FactorialUp.chooseCount_self n

theorem natChooseCount_pascal (n k : Nat) :
    natChooseCount (Nat.succ n) (Nat.succ k) =
      natChooseCount n k + natChooseCount n (Nat.succ k) := by
  change bwordLength (natChooseFn (natToUnary (Nat.succ n)) (natToUnary (Nat.succ k))) =
    bwordLength (natChooseFn (natToUnary n) (natToUnary k)) +
      bwordLength (natChooseFn (natToUnary n) (natToUnary (Nat.succ k)))
  unfold natChooseFn
  repeat rw [natToUnary_length]
  rfl

theorem bellRecurrencePrefix_zero (B : Nat -> Nat) (n : Nat) :
    bellRecurrencePrefix B n 0 = natChooseCount n 0 * B 0 := by
  rfl

theorem bellRecurrencePrefix_succ (B : Nat -> Nat) (n k : Nat) :
    bellRecurrencePrefix B n (Nat.succ k) =
      bellRecurrencePrefix B n k + natChooseCount n (Nat.succ k) * B (Nat.succ k) := by
  rfl

theorem bellRecurrenceSum_definition (n : Nat) :
    bellRecurrenceSum n = bellRecurrencePrefix bellNumber n n := by
  rfl

theorem bellNumberByRecurrence_zero :
    bellNumberByRecurrence 0 = 1 := by
  rfl

theorem bellNumberByRecurrence_recurrence (n : Nat) :
    bellNumberByRecurrence (Nat.succ n) =
      bellRecurrencePrefix (bellRecurrenceFunction n) n n := by
  unfold bellNumberByRecurrence
  exact bellRecurrenceFunction_succ_diagonal n

theorem nat_ne_succ_add_right : ∀ k extra : Nat, k ≠ Nat.succ (k + extra)
  | 0, _ => by
      intro h
      cases h
  | Nat.succ k, extra => by
      intro h
      rw [Nat.succ_add] at h
      exact nat_ne_succ_add_right k extra (Nat.succ.inj h)

theorem bellRecurrenceFunction_stage_lookup (k extra : Nat) :
    bellRecurrenceFunction (k + extra) k = bellNumberByRecurrence k := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ extra ih =>
      rw [Nat.add_succ]
      unfold bellRecurrenceFunction
      rw [if_neg (nat_ne_succ_add_right k extra)]
      exact ih

theorem nat_succ_add_as_add_succ (k extra : Nat) :
    Nat.succ k + extra = k + Nat.succ extra := by
  rw [Nat.succ_add]
  exact (Nat.add_succ k extra).symm

theorem bellRecurrencePrefix_stage_lookup (Bindex k extra : Nat) :
    bellRecurrencePrefix (bellRecurrenceFunction (k + extra)) Bindex k =
      bellRecurrencePrefix bellNumberByRecurrence Bindex k := by
  induction k generalizing extra with
  | zero =>
      rw [bellRecurrencePrefix_zero, bellRecurrencePrefix_zero]
      rw [bellRecurrenceFunction_stage_lookup 0 extra]
  | succ k ih =>
      rw [bellRecurrencePrefix_succ, bellRecurrencePrefix_succ]
      rw [nat_succ_add_as_add_succ k extra]
      rw [ih (Nat.succ extra)]
      rw [← nat_succ_add_as_add_succ k extra]
      rw [bellRecurrenceFunction_stage_lookup (Nat.succ k) extra]

theorem bellNumberByRecurrence_standard_recurrence (n : Nat) :
    bellNumberByRecurrence (Nat.succ n) =
      bellRecurrencePrefix bellNumberByRecurrence n n := by
  rw [bellNumberByRecurrence_recurrence]
  exact bellRecurrencePrefix_stage_lookup n n 0

theorem bellNumber_zero :
    bellNumber 0 = 1 := by
  rfl

theorem bellNumber_one :
    bellNumber 1 = 1 := by
  rfl

theorem bellNumber_two :
    bellNumber 2 = 2 := by
  rfl

theorem bellNumber_three :
    bellNumber 3 = 5 := by
  rfl

theorem bellNumber_four :
    bellNumber 4 = 15 := by
  rfl

theorem bellNumberByRecurrence_one :
    bellNumberByRecurrence 1 = 1 := by
  rfl

theorem bellNumberByRecurrence_two :
    bellNumberByRecurrence 2 = 2 := by
  rfl

theorem bellNumberByRecurrence_three :
    bellNumberByRecurrence 3 = 5 := by
  rfl

theorem bellNumberByRecurrence_four :
    bellNumberByRecurrence 4 = 15 := by
  rfl

theorem bellNumber_agrees_with_recurrence_at_four :
    bellNumber 4 = bellNumberByRecurrence 4 := by
  rfl

theorem BellNumberUp_constructive_export :
    bellNumber 0 = 1 ∧
      bellNumber 1 = 1 ∧
      bellNumber 2 = 2 ∧
      bellNumber 3 = 5 ∧
      bellNumber 4 = 15 ∧
      (∀ n : Nat,
        bellNumberByRecurrence (Nat.succ n) =
          bellRecurrencePrefix bellNumberByRecurrence n n) := by
  constructor
  · exact bellNumber_zero
  · constructor
    · exact bellNumber_one
    · constructor
      · exact bellNumber_two
      · constructor
        · exact bellNumber_three
        · constructor
          · exact bellNumber_four
          · intro n
            exact bellNumberByRecurrence_standard_recurrence n

end BEDC.Derived.BellNumberUp
