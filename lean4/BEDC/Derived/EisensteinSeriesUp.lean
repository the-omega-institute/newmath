import BEDC.Derived.BernoulliUp
import BEDC.Derived.DivisorFunctionUp
import BEDC.Derived.PrimeUp.UniqueFactorization

namespace BEDC.Derived.EisensteinSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.BernoulliUp
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp

private abbrev NatOne : BHist :=
  BHist.e1 BHist.Empty

def NatTwo : BHist :=
  natToUnary 2

def NatThree : BHist :=
  natToUnary 3

structure EisensteinTruncation where
  weight : Nat
  boundary : Nat
  coefficients : List RatNum

def weightEven (k : Nat) : Prop :=
  ∃ h : Nat, k = h + h

def finiteTruncationBoundary (series : EisensteinTruncation) : Nat :=
  series.boundary

def finiteTruncationCoefficients (series : EisensteinTruncation) : List RatNum :=
  series.coefficients

def finiteTruncationWeightTag (series : EisensteinTruncation) : Nat :=
  series.weight

def rawRatScaleNat (n : Nat) (x : RawRat) : RawRat :=
  rawMulNat n x

def sigmaPowerNat (power : Nat) (profile : PrimePowerProfile) : Nat :=
  divisorSigmaProfileNat power profile

def rawSigmaCoefficient (scale : RawRat) (power : Nat)
    (profile : PrimePowerProfile) : RawRat :=
  rawRatScaleNat (sigmaPowerNat power profile) scale

def sigmaCoefficient (scale : RawRat) (power : Nat)
    (profile : PrimePowerProfile) : RatNum :=
  rawRatToRat (rawSigmaCoefficient scale power profile)

-- 这里只承载 E4/E6 的有限 q 截断系数和权重标签，不声明完整解析模性。
inductive SupportedEisensteinWeight where
  | four : SupportedEisensteinWeight
  | six : SupportedEisensteinWeight
  deriving DecidableEq, Repr

inductive UnitRawBernoulli where
  | positive (denMinusOne : Nat) : UnitRawBernoulli
  | negative (denMinusOne : Nat) : UnitRawBernoulli
  deriving DecidableEq, Repr

def unitRawBernoulliValue : UnitRawBernoulli -> RawRat
  | UnitRawBernoulli.positive denMinusOne =>
      { num := 1, denMinusOne := denMinusOne }
  | UnitRawBernoulli.negative denMinusOne =>
      { num := -1, denMinusOne := denMinusOne }

def unitRawBernoulliQuotientScale (twoWeight : Nat) :
    UnitRawBernoulli -> RawRat
  | UnitRawBernoulli.positive denMinusOne =>
      { num := -(Int.ofNat (twoWeight * Nat.succ denMinusOne)),
        denMinusOne := 0 }
  | UnitRawBernoulli.negative denMinusOne =>
      { num := Int.ofNat (twoWeight * Nat.succ denMinusOne),
        denMinusOne := 0 }

def e4BernoulliUnit : UnitRawBernoulli :=
  UnitRawBernoulli.negative 29

def e6BernoulliUnit : UnitRawBernoulli :=
  UnitRawBernoulli.positive 41

def e4Scale : RawRat :=
  unitRawBernoulliQuotientScale 8 e4BernoulliUnit

def e6Scale : RawRat :=
  unitRawBernoulliQuotientScale 12 e6BernoulliUnit

def supportedEisensteinWeightNat : SupportedEisensteinWeight -> Nat
  | SupportedEisensteinWeight.four => 4
  | SupportedEisensteinWeight.six => 6

def supportedEisensteinSigmaPower : SupportedEisensteinWeight -> Nat
  | SupportedEisensteinWeight.four => 3
  | SupportedEisensteinWeight.six => 5

def supportedEisensteinScale : SupportedEisensteinWeight -> RawRat
  | SupportedEisensteinWeight.four => e4Scale
  | SupportedEisensteinWeight.six => e6Scale

def rawSupportedEisensteinCoefficient
    (weight : SupportedEisensteinWeight) (profile : PrimePowerProfile) : RawRat :=
  rawSigmaCoefficient (supportedEisensteinScale weight)
    (supportedEisensteinSigmaPower weight) profile

def supportedEisensteinCoefficient
    (weight : SupportedEisensteinWeight) (profile : PrimePowerProfile) : RatNum :=
  rawRatToRat (rawSupportedEisensteinCoefficient weight profile)

def eisensteinConstantCoefficient : RatNum :=
  rawRatToRat rawOne

def E4Coefficient (profile : PrimePowerProfile) : RatNum :=
  sigmaCoefficient e4Scale 3 profile

def E6Coefficient (profile : PrimePowerProfile) : RatNum :=
  sigmaCoefficient e6Scale 5 profile

def profileOne : PrimePowerProfile :=
  []

def profileTwo : PrimePowerProfile :=
  [{ prime := NatTwo, exponent := 1 }]

def profileThree : PrimePowerProfile :=
  [{ prime := NatThree, exponent := 1 }]

def E4FiniteTruncation : EisensteinTruncation :=
  { weight := 4
    boundary := 3
    coefficients :=
      [eisensteinConstantCoefficient,
        E4Coefficient profileOne,
        E4Coefficient profileTwo,
        E4Coefficient profileThree] }

def E6FiniteTruncation : EisensteinTruncation :=
  { weight := 6
    boundary := 3
    coefficients :=
      [eisensteinConstantCoefficient,
        E6Coefficient profileOne,
        E6Coefficient profileTwo,
        E6Coefficient profileThree] }

def EisensteinFiniteFamily : List EisensteinTruncation :=
  [E4FiniteTruncation, E6FiniteTruncation]

def CoefficientUsesSigma
    (scale : RawRat) (power : Nat) (profile : PrimePowerProfile) (coeff : RatNum) :
    Prop :=
  RatEq coeff (sigmaCoefficient scale power profile)

def E4CoefficientUsesSigma
    (profile : PrimePowerProfile) (coeff : RatNum) : Prop :=
  CoefficientUsesSigma e4Scale 3 profile coeff

def E6CoefficientUsesSigma
    (profile : PrimePowerProfile) (coeff : RatNum) : Prop :=
  CoefficientUsesSigma e6Scale 5 profile coeff

def coefficientProfileValue (profile : PrimePowerProfile) : Nat :=
  match profile with
  | [] => 1
  | e :: es => natPow (bwordLength e.prime) e.exponent * coefficientProfileValue es

inductive TruncationProfilesWithinFuel (boundary : Nat) :
    Nat -> List PrimePowerProfile -> Prop where
  | nil (fuel : Nat) : TruncationProfilesWithinFuel boundary fuel []
  | cons {fuel : Nat} {profile : PrimePowerProfile}
      {profiles : List PrimePowerProfile} :
      coefficientProfileValue profile <= boundary ->
        TruncationProfilesWithinFuel boundary fuel profiles ->
          TruncationProfilesWithinFuel boundary (fuel + 1) (profile :: profiles)

def TruncationProfilesWithinBounded (boundary : Nat) (profiles : List PrimePowerProfile) :
    Prop :=
  TruncationProfilesWithinFuel boundary boundary profiles

def E4CoefficientProfiles : List PrimePowerProfile :=
  [profileOne, profileTwo, profileThree]

def E6CoefficientProfiles : List PrimePowerProfile :=
  [profileOne, profileTwo, profileThree]

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k ->
      hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        unary_hsame_of_length resultData.left (natToUnary_unary _)
          ((NatMul_bwordLength resultData.right).trans (by
            rw [natToUnary_length, natToUnary_length, natToUnary_length]))
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix NatOne (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append NatOne tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem natOne_strict_natToUnary_succ_succ (n : Nat) :
    NatUnaryStrictPrefix NatOne (natToUnary (Nat.succ (Nat.succ n))) := by
  change NatUnaryStrictPrefix NatOne (BHist.e1 (natToUnary (Nat.succ n)))
  exact natOne_strict_of_tail (natToUnary (Nat.succ n))
    (natToUnary_unary (Nat.succ n)) (fun empty => by
      change BHist.e1 (natToUnary n) = BHist.Empty at empty
      exact not_hsame_e1_empty empty)

theorem NatTwo_prime : NatPrime NatTwo := by
  unfold NatTwo
  exact NatPrime_first_pair.left

theorem NatThree_prime : NatPrime NatThree := by
  unfold NatThree
  exact NatPrime_first_pair.right

theorem profileOne_valid : ProfileValid profileOne := by
  exact ProfileValid.nil

theorem profileTwo_valid : ProfileValid profileTwo := by
  unfold profileTwo
  exact ProfileValid.cons NatTwo_prime (by intro h; cases h) rfl ProfileValid.nil

theorem profileThree_valid : ProfileValid profileThree := by
  unfold profileThree
  exact ProfileValid.cons NatThree_prime (by intro h; cases h) rfl ProfileValid.nil

theorem profileOne_factorization :
    PrimeFactorization NatOne (expandProfile profileOne) := by
  constructor
  · exact unary_e1_closed unary_empty
  · exact hsame_refl NatOne

private theorem primeFactorizationProduct_singleton
    {p : BHist} (pPrime : NatPrime p) :
    PrimeFactorizationProduct [p] p := by
  exact ⟨pPrime, NatOne, hsame_refl NatOne,
    NatMul.succ (NatMul.zero pPrime.left) (cont_left_unit p)⟩

theorem profileTwo_factorization :
    PrimeFactorization NatTwo (expandProfile profileTwo) := by
  constructor
  · unfold NatTwo
    exact natToUnary_unary 2
  · unfold profileTwo expandProfile expandPrimePower
    exact primeFactorizationProduct_singleton NatTwo_prime

theorem profileThree_factorization :
    PrimeFactorization NatThree (expandProfile profileThree) := by
  constructor
  · unfold NatThree
    exact natToUnary_unary 3
  · unfold profileThree expandProfile expandPrimePower
    exact primeFactorizationProduct_singleton NatThree_prime

theorem profileOne_sigma (power : Nat) :
    DivisorSigmaOfProfile power NatOne
      (divisorSigmaProfile power profileOne) profileOne := by
  exact ⟨profileOne_valid, profileOne_factorization,
    hsame_refl (divisorSigmaProfile power profileOne)⟩

theorem profileTwo_sigma (power : Nat) :
    DivisorSigmaOfProfile power NatTwo
      (divisorSigmaProfile power profileTwo) profileTwo := by
  exact ⟨profileTwo_valid, profileTwo_factorization,
    hsame_refl (divisorSigmaProfile power profileTwo)⟩

theorem profileThree_sigma (power : Nat) :
    DivisorSigmaOfProfile power NatThree
      (divisorSigmaProfile power profileThree) profileThree := by
  exact ⟨profileThree_valid, profileThree_factorization,
    hsame_refl (divisorSigmaProfile power profileThree)⟩

theorem weightEven_four : weightEven 4 := by
  exact ⟨2, rfl⟩

theorem weightEven_six : weightEven 6 := by
  exact ⟨3, rfl⟩

theorem e4_weight_tag :
    finiteTruncationWeightTag E4FiniteTruncation = 4 := by
  rfl

theorem e6_weight_tag :
    finiteTruncationWeightTag E6FiniteTruncation = 6 := by
  rfl

theorem e4_even_weight :
    weightEven (finiteTruncationWeightTag E4FiniteTruncation) := by
  exact weightEven_four

theorem e6_even_weight :
    weightEven (finiteTruncationWeightTag E6FiniteTruncation) := by
  exact weightEven_six

theorem e4_finite_boundary :
    finiteTruncationBoundary E4FiniteTruncation = 3 := by
  rfl

theorem e6_finite_boundary :
    finiteTruncationBoundary E6FiniteTruncation = 3 := by
  rfl

theorem e4_coefficients_exact :
    finiteTruncationCoefficients E4FiniteTruncation =
      [eisensteinConstantCoefficient,
        E4Coefficient profileOne,
        E4Coefficient profileTwo,
        E4Coefficient profileThree] := by
  rfl

theorem e6_coefficients_exact :
    finiteTruncationCoefficients E6FiniteTruncation =
      [eisensteinConstantCoefficient,
        E6Coefficient profileOne,
        E6Coefficient profileTwo,
        E6Coefficient profileThree] := by
  rfl

theorem e4_constant_coeff :
    RatEq (E4FiniteTruncation.coefficients.headD ratZero)
      eisensteinConstantCoefficient := by
  exact RatEq_refl _

theorem e6_constant_coeff :
    RatEq (E6FiniteTruncation.coefficients.headD ratZero)
      eisensteinConstantCoefficient := by
  exact RatEq_refl _

theorem E4Coefficient_sigma_link (profile : PrimePowerProfile) :
    E4CoefficientUsesSigma profile (E4Coefficient profile) := by
  exact RatEq_refl _

theorem E6Coefficient_sigma_link (profile : PrimePowerProfile) :
    E6CoefficientUsesSigma profile (E6Coefficient profile) := by
  exact RatEq_refl _

theorem E4_profileOne_sigma_link :
    E4CoefficientUsesSigma profileOne (E4Coefficient profileOne) ∧
      DivisorSigmaOfProfile 3 NatOne
        (divisorSigmaProfile 3 profileOne) profileOne := by
  exact ⟨E4Coefficient_sigma_link profileOne, profileOne_sigma 3⟩

theorem E4_profileTwo_sigma_link :
    E4CoefficientUsesSigma profileTwo (E4Coefficient profileTwo) ∧
      DivisorSigmaOfProfile 3 NatTwo
        (divisorSigmaProfile 3 profileTwo) profileTwo := by
  exact ⟨E4Coefficient_sigma_link profileTwo, profileTwo_sigma 3⟩

theorem E4_profileThree_sigma_link :
    E4CoefficientUsesSigma profileThree (E4Coefficient profileThree) ∧
      DivisorSigmaOfProfile 3 NatThree
        (divisorSigmaProfile 3 profileThree) profileThree := by
  exact ⟨E4Coefficient_sigma_link profileThree, profileThree_sigma 3⟩

theorem E6_profileOne_sigma_link :
    E6CoefficientUsesSigma profileOne (E6Coefficient profileOne) ∧
      DivisorSigmaOfProfile 5 NatOne
        (divisorSigmaProfile 5 profileOne) profileOne := by
  exact ⟨E6Coefficient_sigma_link profileOne, profileOne_sigma 5⟩

theorem E6_profileTwo_sigma_link :
    E6CoefficientUsesSigma profileTwo (E6Coefficient profileTwo) ∧
      DivisorSigmaOfProfile 5 NatTwo
        (divisorSigmaProfile 5 profileTwo) profileTwo := by
  exact ⟨E6Coefficient_sigma_link profileTwo, profileTwo_sigma 5⟩

theorem E6_profileThree_sigma_link :
    E6CoefficientUsesSigma profileThree (E6Coefficient profileThree) ∧
      DivisorSigmaOfProfile 5 NatThree
        (divisorSigmaProfile 5 profileThree) profileThree := by
  exact ⟨E6Coefficient_sigma_link profileThree, profileThree_sigma 5⟩

theorem E4_profiles_within_boundary :
    TruncationProfilesWithinBounded 3 E4CoefficientProfiles := by
  unfold TruncationProfilesWithinBounded
  unfold E4CoefficientProfiles profileOne profileTwo profileThree
  refine TruncationProfilesWithinFuel.cons ?_ ?_
  · decide
  · refine TruncationProfilesWithinFuel.cons ?_ ?_
    · decide
    · refine TruncationProfilesWithinFuel.cons ?_ ?_
      · decide
      · exact TruncationProfilesWithinFuel.nil 0

theorem E6_profiles_within_boundary :
    TruncationProfilesWithinBounded 3 E6CoefficientProfiles := by
  unfold TruncationProfilesWithinBounded
  unfold E6CoefficientProfiles profileOne profileTwo profileThree
  refine TruncationProfilesWithinFuel.cons ?_ ?_
  · decide
  · refine TruncationProfilesWithinFuel.cons ?_ ?_
    · decide
    · refine TruncationProfilesWithinFuel.cons ?_ ?_
      · decide
      · exact TruncationProfilesWithinFuel.nil 0

theorem rawBernoulli_six_value :
    rawBernoulli 6 = { num := 1, denMinusOne := 41 } := by
  rfl

theorem e4_bernoulli_unit_value :
    rawBernoulli 4 = unitRawBernoulliValue e4BernoulliUnit := by
  exact rawBernoulli_four_raw_value

theorem e6_bernoulli_unit_value :
    rawBernoulli 6 = unitRawBernoulliValue e6BernoulliUnit := by
  exact rawBernoulli_six_value

theorem e4_scale_from_unit_bernoulli :
    unitRawBernoulliQuotientScale 8 e4BernoulliUnit = e4Scale := by
  rfl

theorem e6_scale_from_unit_bernoulli :
    unitRawBernoulliQuotientScale 12 e6BernoulliUnit = e6Scale := by
  rfl

theorem rawSupportedEisensteinCoefficient_four_profile (profile : PrimePowerProfile) :
    rawSupportedEisensteinCoefficient SupportedEisensteinWeight.four profile =
      rawSigmaCoefficient e4Scale 3 profile := by
  unfold rawSupportedEisensteinCoefficient
  unfold supportedEisensteinScale supportedEisensteinSigmaPower
  unfold rawSigmaCoefficient sigmaPowerNat e4Scale
  rfl

theorem rawSupportedEisensteinCoefficient_six_profile (profile : PrimePowerProfile) :
    rawSupportedEisensteinCoefficient SupportedEisensteinWeight.six profile =
      rawSigmaCoefficient e6Scale 5 profile := by
  unfold rawSupportedEisensteinCoefficient
  unfold supportedEisensteinScale supportedEisensteinSigmaPower
  unfold rawSigmaCoefficient sigmaPowerNat e6Scale
  rfl

theorem E4Coefficient_from_supported_formula (profile : PrimePowerProfile) :
    RatEq (supportedEisensteinCoefficient SupportedEisensteinWeight.four profile)
      (E4Coefficient profile) := by
  change RatEq
    (rawRatToRat
      (rawSupportedEisensteinCoefficient SupportedEisensteinWeight.four profile))
    (rawRatToRat (rawSigmaCoefficient e4Scale 3 profile))
  rw [rawSupportedEisensteinCoefficient_four_profile]
  exact RatEq_refl _

theorem E6Coefficient_from_supported_formula (profile : PrimePowerProfile) :
    RatEq (supportedEisensteinCoefficient SupportedEisensteinWeight.six profile)
      (E6Coefficient profile) := by
  change RatEq
    (rawRatToRat
      (rawSupportedEisensteinCoefficient SupportedEisensteinWeight.six profile))
    (rawRatToRat (rawSigmaCoefficient e6Scale 5 profile))
  rw [rawSupportedEisensteinCoefficient_six_profile]
  exact RatEq_refl _

theorem E4_coefficient_values_truncated :
    finiteTruncationCoefficients E4FiniteTruncation =
      [ratOfIntOverNat 1 0, ratOfIntOverNat 240 0,
        ratOfIntOverNat 2160 0, ratOfIntOverNat 6720 0] := by
  rfl

theorem E6_coefficient_values_truncated :
    finiteTruncationCoefficients E6FiniteTruncation =
      [ratOfIntOverNat 1 0, ratOfIntOverNat (-504) 0,
        ratOfIntOverNat (-16632) 0, ratOfIntOverNat (-122976) 0] := by
  rfl

end BEDC.Derived.EisensteinSeriesUp
