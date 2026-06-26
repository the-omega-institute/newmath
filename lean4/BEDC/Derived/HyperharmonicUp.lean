import BEDC.Derived.HarmonicUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.RationalUp
import BEDC.Algebra.FiniteFold

namespace BEDC.Derived.HyperharmonicUp

open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.HarmonicUp
open BEDC.Derived.RationalUp

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def hyperharmonicPrefix (f : Nat -> RatNum) : Nat -> RatNum
  | 0 => ratZero
  | Nat.succ n => ratAdd (hyperharmonicPrefix f n) (f (Nat.succ n))

def hyperharmonic : Nat -> Nat -> RatNum
  | 0 => fun _ => ratZero
  | Nat.succ r =>
      match r with
      | 0 => harmonic
      | Nat.succ r' =>
          fun n => hyperharmonicPrefix (fun k => hyperharmonic (Nat.succ r') k) n

def hyperharmonicTerms (r : Nat) : Nat -> List RatNum
  | 0 => []
  | Nat.succ n => hyperharmonic r (Nat.succ n) :: hyperharmonicTerms r n

def hyperharmonicListSum : List RatNum -> RatNum
  | [] => ratZero
  | x :: xs => ratAdd (hyperharmonicListSum xs) x

theorem hyperharmonicPrefix_terms (r n : Nat) :
    hyperharmonicPrefix (fun k => hyperharmonic r k) n =
      hyperharmonicListSum (hyperharmonicTerms r n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change ratAdd (hyperharmonicPrefix (fun k => hyperharmonic r k) n)
          (hyperharmonic r (Nat.succ n)) =
        ratAdd (hyperharmonicListSum (hyperharmonicTerms r n))
          (hyperharmonic r (Nat.succ n))
      exact congrArg (fun x => ratAdd x (hyperharmonic r (Nat.succ n))) ih

theorem hyperharmonic_order_one (n : Nat) :
    RatEq (hyperharmonic 1 n) (harmonic n) := by
  change RatEq (harmonic n) (harmonic n)
  exact RatEq_refl _

theorem hyperharmonic_recursive (r n : Nat) :
    RatEq (hyperharmonic (Nat.succ (Nat.succ r)) (Nat.succ n))
      (ratAdd (hyperharmonic (Nat.succ (Nat.succ r)) n)
        (hyperharmonic (Nat.succ r) (Nat.succ n))) := by
  change RatEq
    (ratAdd (hyperharmonicPrefix (fun k => hyperharmonic (Nat.succ r) k) n)
      (hyperharmonic (Nat.succ r) (Nat.succ n)))
    (ratAdd (hyperharmonicPrefix (fun k => hyperharmonic (Nat.succ r) k) n)
      (hyperharmonic (Nat.succ r) (Nat.succ n)))
  exact RatEq_refl _

theorem hyperharmonic_as_list_sum (r n : Nat) :
    hyperharmonic (Nat.succ (Nat.succ r)) n =
      hyperharmonicListSum (hyperharmonicTerms (Nat.succ r) n) := by
  change hyperharmonicPrefix (fun k => hyperharmonic (Nat.succ r) k) n =
    hyperharmonicListSum (hyperharmonicTerms (Nat.succ r) n)
  exact hyperharmonicPrefix_terms (Nat.succ r) n

def ratOfNat (n : Nat) : RatNum :=
  BEDC.Derived.BernoulliUp.ratOfIntOverNat (Int.ofNat n) 0

def binomialRat (n k : Nat) : RatNum :=
  ratOfNat (C n k)

def hyperharmonicClosedForm (r n : Nat) : RatNum :=
  ratMul (binomialRat (n + r - 1) (r - 1))
    (ratSub (harmonic (n + r - 1)) (harmonic (r - 1)))

def hyperharmonicTwoTwo : RatNum :=
  harmonicRat 5 1

def hyperharmonicTwoThree : RatNum :=
  harmonicRat 13 2

set_option maxRecDepth 4096 in
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

theorem hyperharmonic_two_two_value :
    RatEq (hyperharmonic 2 2) hyperharmonicTwoTwo := by
  apply ratEq_of_cross_length_eq
  decide

theorem hyperharmonic_two_three_value :
    RatEq (hyperharmonic 2 3) hyperharmonicTwoThree := by
  set_option maxRecDepth 4096 in
  apply ratEq_of_cross_length_eq
  decide

theorem hyperharmonic_closed_one_one :
    RatEq (hyperharmonic 1 1) (hyperharmonicClosedForm 1 1) := by
  apply ratEq_of_cross_length_eq
  decide

theorem hyperharmonic_closed_one_two :
    RatEq (hyperharmonic 1 2) (hyperharmonicClosedForm 1 2) := by
  apply ratEq_of_cross_length_eq
  decide

theorem hyperharmonic_closed_two_two :
    RatEq (hyperharmonic 2 2) (hyperharmonicClosedForm 2 2) := by
  set_option maxRecDepth 4096 in
  apply ratEq_of_cross_length_eq
  decide

theorem HyperharmonicUp_constructive_export :
    (∀ n : Nat, RatEq (hyperharmonic 1 n) (harmonic n)) ∧
      (∀ r n : Nat,
        RatEq (hyperharmonic (Nat.succ (Nat.succ r)) (Nat.succ n))
          (ratAdd (hyperharmonic (Nat.succ (Nat.succ r)) n)
            (hyperharmonic (Nat.succ r) (Nat.succ n)))) ∧
      RatEq (hyperharmonic 2 2) (hyperharmonicClosedForm 2 2) := by
  constructor
  · intro n
    exact hyperharmonic_order_one n
  · constructor
    · intro r n
      exact hyperharmonic_recursive r n
    · exact hyperharmonic_closed_two_two

end BEDC.Derived.HyperharmonicUp
