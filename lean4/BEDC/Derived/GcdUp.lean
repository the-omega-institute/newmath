import BEDC.Derived.PadicUp.IntegerTower
import BEDC.Derived.PrimeUp.DividesClosure
import BEDC.Derived.PrimeUp.ResultBoundary
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.RationalUp.FieldLaws

namespace BEDC.Derived.GcdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.IntUp
open BEDC.Derived.RationalUp

def NatGcd (a b g : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory g ∧
    NatDivides g a ∧ NatDivides g b ∧
      ∀ d : BHist, NatDivides d a -> NatDivides d b -> NatDivides d g

theorem NatGcd_left_unary {a b g : BHist} :
    NatGcd a b g -> UnaryHistory a := by
  intro gcd
  exact gcd.left

theorem NatGcd_right_unary {a b g : BHist} :
    NatGcd a b g -> UnaryHistory b := by
  intro gcd
  exact gcd.right.left

theorem NatGcd_result_unary {a b g : BHist} :
    NatGcd a b g -> UnaryHistory g := by
  intro gcd
  exact gcd.right.right.left

theorem NatGcd_dvd_left {a b g : BHist} :
    NatGcd a b g -> NatDivides g a := by
  intro gcd
  exact gcd.right.right.right.left

theorem NatGcd_dvd_right {a b g : BHist} :
    NatGcd a b g -> NatDivides g b := by
  intro gcd
  exact gcd.right.right.right.right.left

theorem NatGcd_greatest {a b g d : BHist} :
    NatGcd a b g -> NatDivides d a -> NatDivides d b -> NatDivides d g := by
  intro gcd
  exact gcd.right.right.right.right.right d

private theorem NatDivides_empty_divisor_succ_absurd {d b : BHist} :
    hsame d BHist.Empty -> NatDivides d b -> UnaryHistory b ->
      (hsame b BHist.Empty -> False) -> False := by
  intro dEmpty divides bUnary bNonempty
  cases dEmpty
  exact bNonempty (NatDivides_empty_left_result_empty divides)

theorem NatGcd_unique_hsame {a b g h : BHist} :
    NatGcd a b g -> NatGcd a b h -> hsame g h := by
  intro left right
  have gDividesH : NatDivides g h :=
    NatGcd_greatest right (NatGcd_dvd_left left) (NatGcd_dvd_right left)
  have hDividesG : NatDivides h g :=
    NatGcd_greatest left (NatGcd_dvd_left right) (NatGcd_dvd_right right)
  exact NatDivides_antisymmetry_hsame
    (NatGcd_result_unary left) (NatGcd_result_unary right) gDividesH hDividesG

theorem NatGcd_zero_right {a : BHist} :
    UnaryHistory a -> NatGcd a BHist.Empty a := by
  intro aUnary
  constructor
  · exact aUnary
  · constructor
    · exact unary_empty
    · constructor
      · exact aUnary
      · constructor
        · exact (NatDivides_reflexive_pair aUnary).right
        · constructor
          · exact NatDivides_empty_right_iff.mpr aUnary
          · intro d dividesA _dividesZero
            exact dividesA

private theorem NatDivRem_divisor_nonempty {b a q r : BHist} :
    NatDivRem b a q r -> hsame b BHist.Empty -> False := by
  intro divrem bEmpty
  cases divrem with
  | intro _mq data =>
      cases bEmpty
      exact NatUnaryStrictPrefix_empty_right_absurd data.right.right

private theorem NatDivRem_common_divisor_remainder {a b q r d : BHist} :
    NatDivRem b a q r -> NatDivides d a -> NatDivides d b -> NatDivides d r := by
  intro divrem dividesA dividesB
  cases divrem with
  | intro bq data =>
      have dUnary : UnaryHistory d := NatDivides_divisor_unary dividesA
      have bNonempty : hsame b BHist.Empty -> False := by
        intro bEmpty
        cases bEmpty
        exact NatUnaryStrictPrefix_empty_right_absurd data.right.right
      have dNonempty : hsame d BHist.Empty -> False := by
        intro dEmpty
        exact NatDivides_empty_divisor_succ_absurd dEmpty dividesB
          (NatMul_left_unary data.left) bNonempty
      have bDividesProduct : NatDivides b bq :=
        ⟨q, NatMul_right_unary data.left, data.left⟩
      have dDividesProduct : NatDivides d bq :=
        NatDivides_transitive dividesB bDividesProduct
      exact dvd_tail_of_dvd_sum dUnary dNonempty data.right.left dDividesProduct dividesA

private theorem NatDivRem_common_divisor_dividend {a b q r d : BHist} :
    NatDivRem b a q r -> NatDivides d b -> NatDivides d r -> NatDivides d a := by
  intro divrem dividesB dividesR
  cases divrem with
  | intro bq data =>
      have bDividesProduct : NatDivides b bq :=
        ⟨q, NatMul_right_unary data.left, data.left⟩
      have dDividesProduct : NatDivides d bq :=
        NatDivides_transitive dividesB bDividesProduct
      exact NatDivides_cont_closed dDividesProduct dividesR data.right.left.right.right

theorem NatGcd_of_divrem {a b q r g : BHist} :
    NatDivRem b a q r -> NatGcd b r g -> NatGcd a b g := by
  intro divrem tailGcd
  constructor
  · exact NatDivRem_dividend_unary divrem
  · constructor
    · exact NatDivRem_divisor_unary divrem
    · constructor
      · exact NatGcd_result_unary tailGcd
      · constructor
        · exact NatDivRem_common_divisor_dividend divrem
            (NatGcd_dvd_left tailGcd) (NatGcd_dvd_right tailGcd)
        · constructor
          · exact NatGcd_dvd_left tailGcd
          · intro d dividesA dividesB
            have dividesR : NatDivides d r :=
              NatDivRem_common_divisor_remainder divrem dividesA dividesB
            exact NatGcd_greatest tailGcd dividesB dividesR

def natGcdFuel : Nat -> BHist -> BHist -> BHist
  | 0, a, _b => a
  | _fuel + 1, a, BHist.Empty => a
  | _fuel + 1, a, BHist.e0 _tail => a
  | fuel + 1, a, BHist.e1 tail =>
      natGcdFuel fuel (BHist.e1 tail) (natModFn (BHist.e1 tail) a)

def natGcdFn (a b : BHist) : BHist :=
  natGcdFuel (BEDC.FKernel.ExternalBinary.bwordLength b + 1) a b

theorem natGcdFuel_spec {fuel : Nat} {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      BEDC.FKernel.ExternalBinary.bwordLength b < fuel ->
        NatGcd a b (natGcdFuel fuel a b) := by
  intro aUnary bUnary fuelEnough
  induction fuel generalizing a b with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ fuelEnough)
  | succ fuel ih =>
      cases b with
      | Empty =>
          exact NatGcd_zero_right aUnary
      | e0 tail =>
          cases bUnary
      | e1 tail =>
          have bNonempty : hsame (BHist.e1 tail) BHist.Empty -> False := by
            intro empty
            exact not_hsame_e1_empty empty
          have remUnary : UnaryHistory (natModFn (BHist.e1 tail) a) :=
            natModFn_unary (unary_e1_closed bUnary) aUnary bNonempty
          have remStrict :
              NatUnaryStrictPrefix (natModFn (BHist.e1 tail) a) (BHist.e1 tail) :=
            natModFn_lt (unary_e1_closed bUnary) aUnary bNonempty
          have remLengthLtB :
              BEDC.FKernel.ExternalBinary.bwordLength (natModFn (BHist.e1 tail) a) <
                BEDC.FKernel.ExternalBinary.bwordLength (BHist.e1 tail) :=
            NatUnaryStrictPrefix_length_lt remUnary remStrict
          have bLengthLeFuel :
              BEDC.FKernel.ExternalBinary.bwordLength (BHist.e1 tail) ≤ fuel :=
            Nat.lt_succ_iff.mp fuelEnough
          have remFuelEnough :
              BEDC.FKernel.ExternalBinary.bwordLength (natModFn (BHist.e1 tail) a) < fuel :=
            Nat.lt_of_lt_of_le remLengthLtB bLengthLeFuel
          have tailGcd :
              NatGcd (BHist.e1 tail) (natModFn (BHist.e1 tail) a)
                (natGcdFuel fuel (BHist.e1 tail) (natModFn (BHist.e1 tail) a)) :=
            ih (unary_e1_closed bUnary) remUnary remFuelEnough
          have divrem :
              NatDivRem (BHist.e1 tail) a
                (natQuotFn (BHist.e1 tail) a) (natModFn (BHist.e1 tail) a) :=
            natModFn_spec (unary_e1_closed bUnary) aUnary bNonempty
          exact NatGcd_of_divrem divrem tailGcd

theorem natGcdFn_spec {a b : BHist} :
    UnaryHistory a -> UnaryHistory b -> NatGcd a b (natGcdFn a b) := by
  intro aUnary bUnary
  unfold natGcdFn
  exact natGcdFuel_spec aUnary bUnary (Nat.lt_succ_self _)

def NatBezoutEquation (a b g : BHist) (x y : BHist × BHist) : Prop :=
  IntPairCarrier x.1 x.2 ∧ IntPairCarrier y.1 y.2 ∧
    IntPairClassifier
      (pairAdd (pairMul x (a, BHist.Empty)) (pairMul y (b, BHist.Empty)))
      (g, BHist.Empty)

theorem NatBezoutEquation_carriers {a b g : BHist} {x y : BHist × BHist} :
    NatBezoutEquation a b g x y ->
      IntPairCarrier x.1 x.2 ∧ IntPairCarrier y.1 y.2 := by
  intro bezout
  exact ⟨bezout.left, bezout.right.left⟩

private theorem IntPairClassifier_trans_pair {x y z : BHist × BHist} :
    IntPairClassifier x y -> IntPairClassifier y z -> IntPairClassifier x z := by
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left

theorem NatBezout_zero_right {a : BHist} :
    UnaryHistory a ->
      NatBezoutEquation a BHist.Empty a
        (NatOne, BHist.Empty) (BHist.Empty, BHist.Empty) := by
  intro aUnary
  have xCarrier : IntPairCarrier NatOne BHist.Empty :=
    ⟨unary_e1_closed unary_empty, unary_empty⟩
  have yCarrier : IntPairCarrier BHist.Empty BHist.Empty :=
    ⟨unary_empty, unary_empty⟩
  constructor
  · exact xCarrier
  · constructor
    · exact yCarrier
    · have leftUnit :
          IntPairClassifier (pairMul (NatOne, BHist.Empty) (a, BHist.Empty))
            (a, BHist.Empty) :=
        pairMul_unit_left (a, BHist.Empty) ⟨aUnary, unary_empty⟩
      have rightZero :
          IntPairClassifier (pairMul (BHist.Empty, BHist.Empty) (BHist.Empty, BHist.Empty))
            (BHist.Empty, BHist.Empty) :=
        pairMul_zero_right (BHist.Empty, BHist.Empty) yCarrier
      have addTransport :
          IntPairClassifier
            (pairAdd (pairMul (NatOne, BHist.Empty) (a, BHist.Empty))
              (pairMul (BHist.Empty, BHist.Empty) (BHist.Empty, BHist.Empty)))
            (pairAdd (a, BHist.Empty) (BHist.Empty, BHist.Empty)) :=
        pairAdd_classifier_congr leftUnit rightZero
      exact IntPairClassifier_trans_pair addTransport
        (pairAdd_zero_right (a, BHist.Empty) ⟨aUnary, unary_empty⟩)

def NatBezoutCoefficients (a b g : BHist) : Prop :=
  ∃ x : BHist × BHist, ∃ y : BHist × BHist,
    NatBezoutEquation a b g x y

def natBezoutFuel : Nat -> BHist -> BHist -> (BHist × BHist) × (BHist × BHist)
  | 0, _a, _b => ((BHist.Empty, BHist.Empty), (BHist.Empty, BHist.Empty))
  | _fuel + 1, _a, BHist.Empty =>
      (((BEDC.Derived.PadicUp.NatOne), BHist.Empty), (BHist.Empty, BHist.Empty))
  | _fuel + 1, _a, BHist.e0 _tail =>
      ((BHist.Empty, BHist.Empty), (BHist.Empty, BHist.Empty))
  | fuel + 1, a, BHist.e1 tail =>
      let recCoeffs := natBezoutFuel fuel (BHist.e1 tail) (natModFn (BHist.e1 tail) a)
      let x := recCoeffs.1
      let y := recCoeffs.2
      let q := natQuotFn (BHist.e1 tail) a
      (y, BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y))

def natBezoutFn (a b : BHist) : (BHist × BHist) × (BHist × BHist) :=
  natBezoutFuel (BEDC.FKernel.ExternalBinary.bwordLength b + 1) a b

private theorem nat_pair_sub_carrier {x y : BHist × BHist} :
    IntPairCarrier x.1 x.2 -> IntPairCarrier y.1 y.2 ->
      IntPairCarrier (BEDC.Derived.IntUp.intSub x y).1
        (BEDC.Derived.IntUp.intSub x y).2 := by
  intro hx hy
  exact intSub_carrier hx hy

theorem natBezoutFuel_carrier {fuel : Nat} {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      IntPairCarrier (natBezoutFuel fuel a b).1.1 (natBezoutFuel fuel a b).1.2 ∧
        IntPairCarrier (natBezoutFuel fuel a b).2.1 (natBezoutFuel fuel a b).2.2 := by
  intro aUnary bUnary
  induction fuel generalizing a b with
  | zero =>
      exact ⟨⟨unary_empty, unary_empty⟩, ⟨unary_empty, unary_empty⟩⟩
  | succ fuel ih =>
      cases b with
      | Empty =>
          exact
            ⟨⟨unary_e1_closed unary_empty, unary_empty⟩,
              ⟨unary_empty, unary_empty⟩⟩
      | e0 tail =>
          cases bUnary
      | e1 tail =>
          have bNonempty : hsame (BHist.e1 tail) BHist.Empty -> False := by
            intro empty
            exact not_hsame_e1_empty empty
          have remUnary : UnaryHistory (natModFn (BHist.e1 tail) a) :=
            natModFn_unary (unary_e1_closed bUnary) aUnary bNonempty
          let recCoeffs :=
            natBezoutFuel fuel (BHist.e1 tail) (natModFn (BHist.e1 tail) a)
          let x := recCoeffs.1
          let y := recCoeffs.2
          have recCarrier :
              IntPairCarrier x.1 x.2 ∧ IntPairCarrier y.1 y.2 := by
            exact ih (unary_e1_closed bUnary) remUnary
          have qUnary : UnaryHistory (natQuotFn (BHist.e1 tail) a) :=
            NatDivRem_quotient_unary
              (natModFn_spec (unary_e1_closed bUnary) aUnary bNonempty)
          have qPairCarrier : IntPairCarrier (natQuotFn (BHist.e1 tail) a) BHist.Empty :=
            ⟨qUnary, unary_empty⟩
          change
            IntPairCarrier y.1 y.2 ∧
              IntPairCarrier
                (BEDC.Derived.IntUp.intSub x (pairMul (natQuotFn (BHist.e1 tail) a, BHist.Empty) y)).1
                (BEDC.Derived.IntUp.intSub x (pairMul (natQuotFn (BHist.e1 tail) a, BHist.Empty) y)).2
          exact
            ⟨recCarrier.right,
              nat_pair_sub_carrier recCarrier.left
                (pairMul_carrier qPairCarrier recCarrier.right)⟩

theorem natBezoutFn_carrier {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      IntPairCarrier (natBezoutFn a b).1.1 (natBezoutFn a b).1.2 ∧
        IntPairCarrier (natBezoutFn a b).2.1 (natBezoutFn a b).2.2 := by
  intro aUnary bUnary
  unfold natBezoutFn
  exact natBezoutFuel_carrier aUnary bUnary

end BEDC.Derived.GcdUp
