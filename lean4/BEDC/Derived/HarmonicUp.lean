import BEDC.Derived.BernoulliUp
import BEDC.Derived.RationalUp
import BEDC.Algebra.FiniteFold

namespace BEDC.Derived.HarmonicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.RationalUp

private abbrev unaryOne : BHist :=
  BHist.e1 BHist.Empty

private theorem natToUnary_one_left_cont (n : Nat) :
    BEDC.FKernel.Cont.Cont unaryOne (natToUnary n) (natToUnary (Nat.succ n)) := by
  induction n with
  | zero =>
      rfl
  | succ _ ih =>
      change BHist.e1 (natToUnary _) =
        BHist.e1 (BEDC.FKernel.Cont.append unaryOne _)
      exact congrArg BHist.e1 ih

private theorem natToUnary_succ_pos (n : Nat) :
    BEDC.Derived.NatUp.NatUnaryStrictPrefix unaryOne
        (natToUnary (Nat.succ (Nat.succ n))) ∨
      hsame (natToUnary (Nat.succ (Nat.succ n))) unaryOne := by
  exact Or.inl
    ⟨natToUnary (Nat.succ n), natToUnary_unary (Nat.succ n),
      (fun empty => by cases empty),
      natToUnary_one_left_cont (Nat.succ n)⟩

private theorem natToUnary_one_pos :
    BEDC.Derived.NatUp.NatUnaryStrictPrefix unaryOne (natToUnary 1) ∨
      hsame (natToUnary 1) unaryOne := by
  exact Or.inr rfl

def harmonicRat (num : Int) (den : Nat) : RatNum :=
  BEDC.Derived.BernoulliUp.ratOfIntOverNat num den

def oneOverNatSucc : Nat -> RatNum
  | 0 => harmonicRat 1 0
  | Nat.succ n =>
      { num := BEDC.Derived.BernoulliUp.intOfLeanInt 1
        den := natToUnary (Nat.succ (Nat.succ n))
        den_pos := natToUnary_succ_pos n }

def harmonic : Nat -> RatNum
  | 0 => ratZero
  | Nat.succ n => ratAdd (harmonic n) (oneOverNatSucc n)

def harmonicTerms : Nat -> List RatNum
  | 0 => []
  | Nat.succ n => oneOverNatSucc n :: harmonicTerms n

def ratListSum : List RatNum -> RatNum
  | [] => ratZero
  | x :: xs => ratAdd (ratListSum xs) x

theorem harmonic_as_sum (n : Nat) :
    harmonic n = ratListSum (harmonicTerms n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change ratAdd (harmonic n) (oneOverNatSucc n) =
        ratAdd (ratListSum (harmonicTerms n)) (oneOverNatSucc n)
      exact congrArg (fun h => ratAdd h (oneOverNatSucc n)) ih

theorem harmonic_zero :
    RatEq (harmonic 0) ratZero := by
  exact RatEq_refl ratZero

theorem harmonic_succ (n : Nat) :
    RatEq (harmonic (Nat.succ n)) (ratAdd (harmonic n) (oneOverNatSucc n)) := by
  exact RatEq_refl _

def harmonicOne : RatNum :=
  harmonicRat 1 0

def harmonicTwo : RatNum :=
  harmonicRat 3 1

def harmonicThree : RatNum :=
  harmonicRat 11 5

def harmonicFour : RatNum :=
  harmonicRat 25 11

theorem oneOverNatSucc_one :
    RatEq (oneOverNatSucc 0) harmonicOne := by
  exact RatEq_refl _

set_option maxRecDepth 2048 in
private theorem ratEq_of_cross_length_eq (x y : RatNum) :
    bwordLength
        (intToPair (intMul x.num (intOfNat y.den (ratDenCarrier y)))).1 +
      bwordLength
        (intToPair (intMul y.num (intOfNat x.den (ratDenCarrier x)))).2 =
      bwordLength
        (intToPair (intMul y.num (intOfNat x.den (ratDenCarrier x)))).1 +
      bwordLength
        (intToPair (intMul x.num (intOfNat y.den (ratDenCarrier y)))).2 ->
    RatEq x y := by
  intro lengthEq
  unfold RatEq
  exact IntPairClassifier_of_length_eq
    (RatEq_cross_carrier_left x y) (RatEq_cross_carrier_right x y) lengthEq

theorem harmonic_one :
    RatEq (harmonic 1) harmonicOne := by
  apply ratEq_of_cross_length_eq
  decide

theorem harmonic_two :
    RatEq (harmonic 2) harmonicTwo := by
  apply ratEq_of_cross_length_eq
  decide

theorem harmonic_three :
    RatEq (harmonic 3) harmonicThree := by
  apply ratEq_of_cross_length_eq
  decide

theorem harmonic_four :
    RatEq (harmonic 4) harmonicFour := by
  set_option maxRecDepth 2048 in
  apply ratEq_of_cross_length_eq
  decide

theorem harmonic_small_values :
    RatEq (harmonic 1) harmonicOne ∧
      RatEq (harmonic 2) harmonicTwo ∧
      RatEq (harmonic 3) harmonicThree ∧
        RatEq (harmonic 4) harmonicFour := by
  exact ⟨harmonic_one, harmonic_two, harmonic_three, harmonic_four⟩

def RatPositive (x : RatNum) : Prop :=
  x.num.sign = BEDC.FKernel.Mark.BMark.b0 ∧
    BEDC.Derived.RationalUp.IntNonzero x.num

theorem oneOverNatSucc_positive (n : Nat) :
    RatPositive (oneOverNatSucc n) := by
  cases n with
  | zero =>
      constructor
      · rfl
      · exact natToUnary_one_pos
  | succ n =>
      constructor
      · rfl
      · exact natToUnary_one_pos

theorem harmonic_step_positive (n : Nat) :
    RatPositive (oneOverNatSucc n) ∧
      RatEq (harmonic (Nat.succ n)) (ratAdd (harmonic n) (oneOverNatSucc n)) := by
  exact ⟨oneOverNatSucc_positive n, harmonic_succ n⟩

theorem harmonic_monotone_step (n : Nat) :
    ∃ step : RatNum,
      RatPositive step ∧
        RatEq (harmonic (Nat.succ n)) (ratAdd (harmonic n) step) := by
  exact ⟨oneOverNatSucc n, oneOverNatSucc_positive n, harmonic_succ n⟩

end BEDC.Derived.HarmonicUp
