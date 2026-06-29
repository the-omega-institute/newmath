import BEDC.Derived.BellNumberUp
import BEDC.Derived.ZModUp

namespace BEDC.Derived.BellNumberModUp

open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp

abbrev bellNumber : Nat -> Nat :=
  BEDC.Derived.BellNumberUp.bellNumber

def bellMod (p n : Nat) : Nat :=
  bellNumber n % p

def bellNumberZMod (p n : Nat) (prime : NatPrime (natToUnary p)) :
    ZMod (natToUnary p) :=
  zmodFromNat (natToUnary p) prime.left (NatPrime_empty_absurd prime)
    (natToUnary (bellNumber n)) (natToUnary_unary (bellNumber n))

def touchardCongruenceAt (p n : Nat) : Prop :=
  bellMod p (n + p) = (bellMod p n + bellMod p (n + 1)) % p

def touchardCongruenceHoldsAt (p n : Nat) : Bool :=
  Nat.beq (bellMod p (n + p)) ((bellMod p n + bellMod p (n + 1)) % p)

def touchardCongruenceWindowFrom (p start fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | Nat.succ f =>
      touchardCongruenceHoldsAt p start &&
        touchardCongruenceWindowFrom p (start + 1) f

def touchardCongruenceWindow (p fuel : Nat) : Bool :=
  touchardCongruenceWindowFrom p 0 fuel

theorem boolAnd_true_left {a b : Bool} :
    (a && b) = true -> a = true := by
  cases a with
  | false =>
      intro checked
      cases b <;> cases checked
  | true =>
      intro _
      rfl

theorem boolAnd_true_right {a b : Bool} :
    (a && b) = true -> b = true := by
  cases b with
  | false =>
      intro checked
      cases a <;> cases checked
  | true =>
      intro _
      rfl

theorem touchardCongruenceHoldsAt_sound {p n : Nat} :
    touchardCongruenceHoldsAt p n = true -> touchardCongruenceAt p n := by
  intro checked
  unfold touchardCongruenceHoldsAt at checked
  unfold touchardCongruenceAt
  exact Nat.eq_of_beq_eq_true checked

theorem touchardCongruenceWindowFrom_sound {p start fuel : Nat} :
    touchardCongruenceWindowFrom p start fuel = true ->
      forall offset : Nat, offset < fuel ->
        touchardCongruenceAt p (start + offset) := by
  intro checked
  induction fuel generalizing start with
  | zero =>
      intro offset offsetLt
      exact False.elim (Nat.not_lt_zero offset offsetLt)
  | succ fuel ih =>
      intro offset offsetLt
      unfold touchardCongruenceWindowFrom at checked
      have headChecked :
          touchardCongruenceHoldsAt p start = true :=
        boolAnd_true_left checked
      have tailChecked :
          touchardCongruenceWindowFrom p (start + 1) fuel = true :=
        boolAnd_true_right checked
      cases offset with
      | zero =>
          exact touchardCongruenceHoldsAt_sound headChecked
      | succ offset =>
          have offsetTailLt : offset < fuel :=
            Nat.lt_of_succ_lt_succ offsetLt
          have tailAt :
              touchardCongruenceAt p ((start + 1) + offset) :=
            ih tailChecked offset offsetTailLt
          have indexShape : (start + 1) + offset = start + Nat.succ offset := by
            rw [Nat.add_assoc]
            rw [Nat.one_add]
          rw [indexShape] at tailAt
          exact tailAt

theorem touchardCongruenceWindow_sound {p fuel : Nat} :
    touchardCongruenceWindow p fuel = true ->
      forall n : Nat, n < fuel -> touchardCongruenceAt p n := by
  intro checked n nLt
  simpa using touchardCongruenceWindowFrom_sound checked n nLt

def bellResidueState (p n : Nat) : Nat × Nat :=
  (bellMod p n, bellMod p (n + 1))

def bellResidueStatePeriodAt (p period : Nat) : Prop :=
  0 < period ∧ forall n : Nat, bellResidueState p (n + period) = bellResidueState p n

def touchardPeriodBound (p : Nat) : Nat :=
  (p ^ p - 1) / (p - 1)

def bellResidueStatePeriodHoldsAt (p period fuel : Nat) : Bool :=
  match period with
  | 0 => false
  | Nat.succ _ =>
      (List.range fuel).all
        (fun n => bellResidueState p (n + period) == bellResidueState p n)

theorem bellMod_zero :
    bellMod 2 2 = 0 := by
  rfl

theorem bellMod_three_four :
    bellMod 3 4 = 0 := by
  rfl

theorem bellNumberZMod_two_two_zero :
    zmodEq (bellNumberZMod 2 2 NatPrime_first_pair.left)
      (zmodZero (natToUnary 2) NatPrime_first_pair.left.left
        (NatPrime_empty_absurd NatPrime_first_pair.left)) := by
  unfold bellNumberZMod zmodZero zmodFromNat zmodEq bellNumber
  rfl

theorem touchard_congruence_mod_two_n_zero :
    touchardCongruenceAt 2 0 := by
  unfold touchardCongruenceAt bellMod bellNumber
  decide

theorem touchard_congruence_mod_three_n_four :
    touchardCongruenceAt 3 4 := by
  unfold touchardCongruenceAt bellMod bellNumber
  decide

theorem touchard_congruence_mod_two_window :
    touchardCongruenceWindow 2 32 = true := by
  decide

theorem touchard_congruence_mod_three_window :
    touchardCongruenceWindow 3 24 = true := by
  decide

theorem touchard_congruence_mod_five_window :
    touchardCongruenceWindow 5 16 = true := by
  decide

theorem touchard_congruence_mod_two_window_sound :
    forall n : Nat, n < 32 -> touchardCongruenceAt 2 n := by
  exact touchardCongruenceWindow_sound touchard_congruence_mod_two_window

theorem touchard_congruence_mod_three_window_sound :
    forall n : Nat, n < 24 -> touchardCongruenceAt 3 n := by
  exact touchardCongruenceWindow_sound touchard_congruence_mod_three_window

theorem touchard_congruence_mod_five_window_sound :
    forall n : Nat, n < 16 -> touchardCongruenceAt 5 n := by
  exact touchardCongruenceWindow_sound touchard_congruence_mod_five_window

theorem touchard_period_bound_two :
    touchardPeriodBound 2 = 3 := by
  rfl

theorem touchard_period_bound_three :
    touchardPeriodBound 3 = 13 := by
  rfl

theorem bell_residue_state_period_mod_two_three_window :
    bellResidueStatePeriodHoldsAt 2 (touchardPeriodBound 2) 48 = true := by
  decide

theorem bell_residue_state_period_mod_three_thirteen_window :
    bellResidueStatePeriodHoldsAt 3 (touchardPeriodBound 3) 39 = true := by
  decide

theorem BellNumberModUp_constructive_export :
    touchardCongruenceAt 2 0 ∧
      touchardCongruenceAt 3 4 ∧
      touchardCongruenceWindow 2 32 = true ∧
      touchardCongruenceWindow 3 24 = true ∧
      touchardCongruenceWindow 5 16 = true ∧
      touchardPeriodBound 2 = 3 ∧
      touchardPeriodBound 3 = 13 ∧
      bellResidueStatePeriodHoldsAt 2 (touchardPeriodBound 2) 48 = true ∧
      bellResidueStatePeriodHoldsAt 3 (touchardPeriodBound 3) 39 = true := by
  exact ⟨touchard_congruence_mod_two_n_zero,
    touchard_congruence_mod_three_n_four,
    touchard_congruence_mod_two_window,
    touchard_congruence_mod_three_window,
    touchard_congruence_mod_five_window,
    touchard_period_bound_two,
    touchard_period_bound_three,
    bell_residue_state_period_mod_two_three_window,
    bell_residue_state_period_mod_three_thirteen_window⟩

end BEDC.Derived.BellNumberModUp
