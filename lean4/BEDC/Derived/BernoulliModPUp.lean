import BEDC.Derived.KummerCongruenceUp
import BEDC.Derived.ZModUp

namespace BEDC.Derived.BernoulliModPUp

open BEDC.FKernel.Hist
open BEDC.Derived.IntUp (natToUnary)
open BEDC.Derived.PrimeUp
open BEDC.Derived.BernoulliUp
open BEDC.Derived.VonStaudtClausenUp
open BEDC.Derived.KummerCongruenceUp
open BEDC.Derived.ZModUp

def rawResidueRat (r : Nat) : RawRat :=
  { num := Int.ofNat r, denMinusOne := 0 }

def rawBernoulliModP (p n r : Nat) : Prop :=
  rawRatCongruentMod p (rawBernoulli n) (rawResidueRat r)

def rawBernoulliOverIndexModP (p n r : Nat) : Prop :=
  rawRatCongruentMod p (rawBernoulliOverIndex n) (rawResidueRat r)

def natListSum : List Nat -> Nat
  | [] => 0
  | n :: ns => n + natListSum ns

def positiveResiduesNat (p : Nat) : List Nat :=
  (List.range (p - 1)).map Nat.succ

def voronoiFloorTerm (p a n j : Nat) : Nat :=
  (j ^ (n - 1)) * ((a * j) / p)

def voronoiFloorSum (p a n : Nat) : Nat :=
  natListSum ((positiveResiduesNat p).map (fun j => voronoiFloorTerm p a n j))

def rawVoronoiLeft (a n : Nat) : RawRat :=
  rawRatDivNat (rawMulNat (a ^ n - 1) (rawBernoulli n)) n

def rawVoronoiRight (p a n : Nat) : RawRat :=
  rawResidueRat ((a ^ (n - 1)) * voronoiFloorSum p a n)

def voronoiCongruenceAt (p a n : Nat) : Prop :=
  rawRatCongruentMod p (rawVoronoiLeft a n) (rawVoronoiRight p a n)

def rawBernoulliNumeratorResidueHist (p n : Nat) : BHist :=
  natToUnary (intModNat (rawBernoulli n).num p)

def rawBernoulliNumeratorZMod (p n : Nat)
    (prime : NatPrime (natToUnary p)) : ZMod (natToUnary p) :=
  zmodFromNat (natToUnary p) prime.left (NatPrime_empty_absurd prime)
    (rawBernoulliNumeratorResidueHist p n)
    (BEDC.Derived.IntUp.natToUnary_unary
      (intModNat (rawBernoulli n).num p))

def vscPrimeWitnessesForEvenIndex (n : Nat) : List Nat :=
  clausePrimeCandidates (n / 2)

def vscClausenIntegralForEvenIndex (n : Nat) : Prop :=
  rawRatIntegral (rawClausenSum (n / 2) (vscPrimeWitnessesForEvenIndex n))

def vscDenominatorMatchesForEvenIndex (n : Nat) : Prop :=
  rawBernoulliDenominator n = clauseDenominatorProductNat (n / 2)

def voronoiKummerCongruenceAt (p m n : Nat) : Prop :=
  kummerCongruenceAt p m n

def evenIndicesFuel : Nat -> Nat -> List Nat
  | 0, _start => []
  | Nat.succ fuel, start => start :: evenIndicesFuel fuel (start + 2)

def regularPrimeIndexList (p : Nat) : List Nat :=
  evenIndicesFuel ((p - 3) / 2) 2

def intModNatNonzeroBool (z : Int) (p : Nat) : Bool :=
  !(Nat.beq (intModNat z p) 0)

def bernoulliNumeratorUnitModBool (p n : Nat) : Bool :=
  intModNatNonzeroBool (rawBernoulli n).num p

def regularPrimeBernoulliCriterionBool (p : Nat) : Bool :=
  (regularPrimeIndexList p).all (fun n => bernoulliNumeratorUnitModBool p n)

def regularPrimeBernoulliCriterionAt (p : Nat) : Prop :=
  regularPrimeBernoulliCriterionBool p = true

structure RegularPrimeBernoulliCriterion (p : Nat) where
  prime : NatPrime (natToUnary p)
  bernoulli_numerators_nonzero : regularPrimeBernoulliCriterionAt p

theorem bernoulli_two_mod_five_one :
    rawBernoulliModP 5 2 1 := by
  unfold rawBernoulliModP rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem bernoulli_four_mod_seven_three :
    rawBernoulliModP 7 4 3 := by
  unfold rawBernoulliModP rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem bernoulli_six_mod_five_three :
    rawBernoulliModP 5 6 3 := by
  unfold rawBernoulliModP rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem bernoulli_modp_small_values :
    rawBernoulliModP 5 2 1 ∧
      rawBernoulliModP 7 4 3 ∧
        rawBernoulliModP 5 6 3 := by
  exact ⟨bernoulli_two_mod_five_one,
    bernoulli_four_mod_seven_three,
    bernoulli_six_mod_five_three⟩

theorem bernoulli_two_numerator_zmod_five_one :
    zmodEq
      (rawBernoulliNumeratorZMod 5 2
        BEDC.Derived.VonStaudtClausenUp.NatFive_prime)
      (zmodOne (natToUnary 5)
        BEDC.Derived.VonStaudtClausenUp.NatFive_prime.left
        (NatPrime_empty_absurd
          BEDC.Derived.VonStaudtClausenUp.NatFive_prime)) := by
  unfold rawBernoulliNumeratorZMod rawBernoulliNumeratorResidueHist
  unfold zmodOne zmodFromNat zmodEq intModNat rawBernoulli
  rfl

theorem vsc_even_index_two_integral :
    vscClausenIntegralForEvenIndex 2 := by
  rfl

theorem vsc_even_index_four_integral :
    vscClausenIntegralForEvenIndex 4 := by
  rfl

theorem vsc_even_index_six_integral :
    vscClausenIntegralForEvenIndex 6 := by
  rfl

theorem vsc_even_index_two_denominator :
    vscDenominatorMatchesForEvenIndex 2 := by
  rfl

theorem vsc_even_index_four_denominator :
    vscDenominatorMatchesForEvenIndex 4 := by
  rfl

theorem vsc_even_index_six_denominator :
    vscDenominatorMatchesForEvenIndex 6 := by
  rfl

theorem small_vonStaudtClausen_modp_window :
    vscClausenIntegralForEvenIndex 2 ∧
      vscDenominatorMatchesForEvenIndex 2 ∧
        vscClausenIntegralForEvenIndex 4 ∧
          vscDenominatorMatchesForEvenIndex 4 ∧
            vscClausenIntegralForEvenIndex 6 ∧
              vscDenominatorMatchesForEvenIndex 6 := by
  exact ⟨vsc_even_index_two_integral,
    vsc_even_index_two_denominator,
    vsc_even_index_four_integral,
    vsc_even_index_four_denominator,
    vsc_even_index_six_integral,
    vsc_even_index_six_denominator⟩

theorem bernoulli_over_index_two_mod_five_three :
    rawBernoulliOverIndexModP 5 2 3 := by
  unfold rawBernoulliOverIndexModP rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem bernoulli_over_index_six_mod_five_three :
    rawBernoulliOverIndexModP 5 6 3 := by
  unfold rawBernoulliOverIndexModP rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem bernoulli_over_index_two_mod_seven_three :
    rawBernoulliOverIndexModP 7 2 3 := by
  unfold rawBernoulliOverIndexModP rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem bernoulli_over_index_eight_mod_seven_three :
    rawBernoulliOverIndexModP 7 8 3 := by
  unfold rawBernoulliOverIndexModP rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem positiveResiduesNat_five :
    positiveResiduesNat 5 = [1, 2, 3, 4] := by
  rfl

theorem positiveResiduesNat_seven :
    positiveResiduesNat 7 = [1, 2, 3, 4, 5, 6] := by
  rfl

theorem voronoiFloorSum_five_two_two :
    voronoiFloorSum 5 2 2 = 7 := by
  rfl

theorem voronoiFloorSum_seven_two_two :
    voronoiFloorSum 7 2 2 = 15 := by
  rfl

theorem voronoiFloorSum_seven_two_four :
    voronoiFloorSum 7 2 4 = 405 := by
  rfl

theorem voronoi_mod_five_two_two :
    voronoiCongruenceAt 5 2 2 := by
  unfold voronoiCongruenceAt rawVoronoiLeft rawVoronoiRight
  unfold rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem voronoi_mod_seven_two_two :
    voronoiCongruenceAt 7 2 2 := by
  unfold voronoiCongruenceAt rawVoronoiLeft rawVoronoiRight
  unfold rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem voronoi_mod_seven_two_four :
    voronoiCongruenceAt 7 2 4 := by
  unfold voronoiCongruenceAt rawVoronoiLeft rawVoronoiRight
  unfold rawResidueRat rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem voronoi_kummer_mod_five_two_six :
    voronoiKummerCongruenceAt 5 2 6 := by
  exact kummer_mod_five_two_six

theorem voronoi_kummer_mod_seven_two_eight :
    voronoiKummerCongruenceAt 7 2 8 := by
  exact kummer_mod_seven_two_eight

theorem small_voronoi_kummer_residue_window :
    rawBernoulliOverIndexModP 5 2 3 ∧
      rawBernoulliOverIndexModP 5 6 3 ∧
        voronoiCongruenceAt 5 2 2 ∧
          voronoiKummerCongruenceAt 5 2 6 ∧
            rawBernoulliOverIndexModP 7 2 3 ∧
              rawBernoulliOverIndexModP 7 8 3 ∧
                voronoiCongruenceAt 7 2 2 ∧
                  voronoiCongruenceAt 7 2 4 ∧
                    voronoiKummerCongruenceAt 7 2 8 := by
  exact ⟨bernoulli_over_index_two_mod_five_three,
    bernoulli_over_index_six_mod_five_three,
    voronoi_mod_five_two_two,
    voronoi_kummer_mod_five_two_six,
    bernoulli_over_index_two_mod_seven_three,
    bernoulli_over_index_eight_mod_seven_three,
    voronoi_mod_seven_two_two,
    voronoi_mod_seven_two_four,
    voronoi_kummer_mod_seven_two_eight⟩

theorem regularPrimeIndexList_five :
    regularPrimeIndexList 5 = [2] := by
  rfl

theorem regularPrimeIndexList_seven :
    regularPrimeIndexList 7 = [2, 4] := by
  rfl

theorem regular_prime_criterion_five :
    regularPrimeBernoulliCriterionAt 5 := by
  rfl

theorem regular_prime_criterion_seven :
    regularPrimeBernoulliCriterionAt 7 := by
  rfl

def regularPrimeCriterionFive : RegularPrimeBernoulliCriterion 5 where
  prime := BEDC.Derived.VonStaudtClausenUp.NatFive_prime
  bernoulli_numerators_nonzero := regular_prime_criterion_five

def regularPrimeCriterionSeven : RegularPrimeBernoulliCriterion 7 where
  prime := BEDC.Derived.VonStaudtClausenUp.NatSeven_prime
  bernoulli_numerators_nonzero := regular_prime_criterion_seven

theorem small_regular_prime_criterion_window :
    regularPrimeBernoulliCriterionAt 5 ∧
      regularPrimeBernoulliCriterionAt 7 := by
  exact ⟨regular_prime_criterion_five, regular_prime_criterion_seven⟩

end BEDC.Derived.BernoulliModPUp
