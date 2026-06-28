import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.PadicUp.IntegerTower

namespace BEDC.Derived.CollatzTrajectoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp (NatDivRem NatDivRem_remainder_unary)

/-!
Collatz 轨道只在有限 fuel 上计算。这里不给出全局终止性断言。
-/

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then
    n / 2
  else
    3 * n + 1

def collatzOrbit : Nat -> Nat -> List Nat
  | 0, n => [n]
  | fuel + 1, n => n :: collatzOrbit fuel (collatzStep n)

def collatzAfter : Nat -> Nat -> Nat
  | 0, n => n
  | fuel + 1, n => collatzAfter fuel (collatzStep n)

def collatzHitsOneWithin : Nat -> Nat -> Bool
  | 0, n => n == 1
  | fuel + 1, n =>
      if n == 1 then
        true
      else
        collatzHitsOneWithin fuel (collatzStep n)

def collatzHitsOneWithinVerified (fuel n : Nat) : Prop :=
  collatzHitsOneWithin fuel n = true

instance collatzHitsOneWithinVerifiedDecidable (fuel n : Nat) :
    Decidable (collatzHitsOneWithinVerified fuel n) :=
  inferInstanceAs (Decidable (collatzHitsOneWithin fuel n = true))

def collatzNoHitBefore : Nat -> Nat -> Bool
  | 0, _n => true
  | fuel + 1, n =>
      if collatzAfter fuel n == 1 then
        false
      else
        collatzNoHitBefore fuel n

def collatzTotalStoppingTimeVerified (fuel n : Nat) : Prop :=
  collatzAfter fuel n = 1 ∧ collatzNoHitBefore fuel n = true

instance collatzTotalStoppingTimeVerifiedDecidable (fuel n : Nat) :
    Decidable (collatzTotalStoppingTimeVerified fuel n) :=
  inferInstanceAs
    (Decidable (collatzAfter fuel n = 1 ∧ collatzNoHitBefore fuel n = true))

def collatzStepUnary (n : Nat) : BHist :=
  natToUnary (collatzStep n)

def collatzTwoUnary : BHist :=
  natToUnary 2

def collatzDivRemByTwo (n : Nat) : Prop :=
  ∃ half : BHist,
    NatDivRem collatzTwoUnary (natToUnary n) half
      (natModFn collatzTwoUnary (natToUnary n))

theorem collatzStep_even_branch {n : Nat} :
    n % 2 = 0 -> collatzStep n = n / 2 := by
  intro evenResidue
  unfold collatzStep
  rw [if_pos evenResidue]

theorem collatzStep_odd_branch {n : Nat} :
    (n % 2 = 0 -> False) -> collatzStep n = 3 * n + 1 := by
  intro oddResidue
  unfold collatzStep
  rw [if_neg oddResidue]

theorem collatzStepUnary_unary (n : Nat) :
    UnaryHistory (collatzStepUnary n) := by
  unfold collatzStepUnary
  exact natToUnary_unary (collatzStep n)

theorem collatzTwoUnary_unary :
    UnaryHistory collatzTwoUnary := by
  unfold collatzTwoUnary
  exact natToUnary_unary 2

theorem collatzTwoUnary_nonempty :
    hsame collatzTwoUnary BHist.Empty -> False := by
  unfold collatzTwoUnary natToUnary
  intro empty
  exact not_hsame_e1_empty empty

theorem collatzDivRemByTwo_verified (n : Nat) :
    collatzDivRemByTwo n := by
  unfold collatzDivRemByTwo
  exact
    ⟨_,
      natModFn_spec collatzTwoUnary_unary (natToUnary_unary n)
        collatzTwoUnary_nonempty⟩

theorem collatzOrbit_zero (n : Nat) :
    collatzOrbit 0 n = [n] := by
  rfl

theorem collatzOrbit_succ (fuel n : Nat) :
    collatzOrbit (fuel + 1) n = n :: collatzOrbit fuel (collatzStep n) := by
  rfl

theorem collatzOrbit_length (fuel n : Nat) :
    (collatzOrbit fuel n).length = fuel + 1 := by
  induction fuel generalizing n with
  | zero =>
      rfl
  | succ fuel ih =>
      change Nat.succ (collatzOrbit fuel (collatzStep n)).length = fuel + 1 + 1
      rw [ih (collatzStep n)]

theorem collatzAfter_zero (n : Nat) :
    collatzAfter 0 n = n := by
  rfl

theorem collatzAfter_succ (fuel n : Nat) :
    collatzAfter (fuel + 1) n = collatzAfter fuel (collatzStep n) := by
  rfl

theorem collatzHitsOneWithin_zero_one :
    collatzHitsOneWithinVerified 0 1 := by
  rfl

theorem collatzHitsOneWithin_succ_start_one (fuel : Nat) :
    collatzHitsOneWithinVerified (fuel + 1) 1 := by
  rfl

theorem collatzAfter_0_0 :
    collatzAfter 0 0 = 0 := by
  rfl

theorem collatzAfter_1_2 :
    collatzAfter 1 2 = 1 := by
  rfl

theorem collatzAfter_2_4 :
    collatzAfter 2 4 = 1 := by
  rfl

theorem collatzAfter_7_3 :
    collatzAfter 7 3 = 1 := by
  rfl

theorem collatzAfter_5_5 :
    collatzAfter 5 5 = 1 := by
  rfl

theorem collatzAfter_19_9 :
    collatzAfter 19 9 = 1 := by
  rfl

theorem collatzSmallFuelHitsOne :
    collatzHitsOneWithinVerified 0 1 ∧
      collatzHitsOneWithinVerified 1 2 ∧
        collatzHitsOneWithinVerified 2 4 ∧
          collatzHitsOneWithinVerified 7 3 ∧
            collatzHitsOneWithinVerified 6 5 ∧ collatzHitsOneWithinVerified 19 9 := by
  decide

theorem collatzSmallTotalStoppingTimes :
    collatzTotalStoppingTimeVerified 0 1 ∧
      collatzTotalStoppingTimeVerified 1 2 ∧
        collatzTotalStoppingTimeVerified 2 4 ∧
          collatzTotalStoppingTimeVerified 7 3 ∧
            collatzTotalStoppingTimeVerified 5 5 ∧
              collatzTotalStoppingTimeVerified 19 9 := by
  decide

theorem collatzOrbit_7_3_exact :
    collatzOrbit 7 3 = [3, 10, 5, 16, 8, 4, 2, 1] := by
  rfl

theorem collatzDivRemByTwo_unary_components (n : Nat) :
    UnaryHistory collatzTwoUnary ∧
      UnaryHistory (natToUnary n) ∧
        UnaryHistory (natModFn collatzTwoUnary (natToUnary n)) := by
  have divremExists := collatzDivRemByTwo_verified n
  cases divremExists with
  | intro _half divrem =>
      constructor
      · exact collatzTwoUnary_unary
      · constructor
        · exact natToUnary_unary n
        · exact NatDivRem_remainder_unary divrem

theorem collatz_mod_two_zero_is_even_step {n : Nat} :
    n % 2 = 0 -> collatzStep n = n / 2 := by
  exact collatzStep_even_branch

theorem collatz_mod_two_nonzero_is_odd_step {n : Nat} :
    (n % 2 = 0 -> False) -> collatzStep n = 3 * n + 1 := by
  exact collatzStep_odd_branch

end BEDC.Derived.CollatzTrajectoryUp
