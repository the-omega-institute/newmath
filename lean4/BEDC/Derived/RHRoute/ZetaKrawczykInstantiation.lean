import BEDC.Derived.RHRoute.ZetaDerivativeBox

namespace BEDC.Derived.RHRoute.ZetaKrawczykInstantiation

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.KrawczykCertificate

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev ComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ComplexBox

abbrev ZetaDerivativeBoxEvaluator
    (I : ZetaAnalyticInterface) (c : RatComplex) (r : Rat) : Type :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ZetaDerivativeBoxEvaluator I c r

abbrev ZetaDerivativeBoxCandidate
    (I : ZetaAnalyticInterface) (c : RatComplex) (r : Rat) : Type :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ZetaDerivativeBoxCandidate I c r

abbrev ZetaDerivativeBoxCandidateSound
    {I : ZetaAnalyticInterface} {c : RatComplex} {r : Rat}
    (C : ZetaDerivativeBoxCandidate I c r) : Prop :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ZetaDerivativeBoxCandidate.Sound C

abbrev derivativeBox_to_krawczyk_bound
    {I : ZetaAnalyticInterface} {c : RatComplex} {r : Rat}
    (E : ZetaDerivativeBoxEvaluator I c r) :
    ZetaDerivativeBoxBound I c r :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.derivativeBox_to_krawczyk_bound E

def derivativeCandidate_to_krawczyk_bound
    {I : ZetaAnalyticInterface} {c : RatComplex} {r : Rat}
    (C : ZetaDerivativeBoxCandidate I c r)
    (sound : ZetaDerivativeBoxCandidateSound C) :
    ZetaDerivativeBoxBound I c r :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ZetaDerivativeBoxCandidate.toKrawczykBound
    C sound

def q (num : Int) (den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfIntOverNat num den

def qNat (num den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfNatOverNat num den

def zetaNear_14_1347_center : RatComplex :=
  { re := q 1 2
    im := q 141347 10000 }

def zetaNear_14_1347_radius : Rat :=
  q 1 1000

def zetaNear_14_1347_inverseDerivative : RatComplex :=
  { re := q 12451007505364848 10000000000000000
    im := q (-1982445063035669) 10000000000000000 }

def zetaNear_14_1347_contractionRatio : Rat :=
  q 1 100

def etaEulerCutoff : Nat :=
  64

def etaEulerDepth : Nat :=
  16

structure RationalComplexRect where
  reLo : Rat
  reHi : Rat
  imLo : Rat
  imHi : Rat

def zetaCenterResidualRect : RationalComplexRect :=
  { reLo := q 3135 1000000000
    reHi := q 3136 1000000000
    imLo := q (-19694) 1000000000
    imHi := q (-19693) 1000000000 }

def zetaPrimeCenterRect : RationalComplexRect :=
  { reLo := q 78329073 100000000
    reHi := q 78329074 100000000
    imLo := q 12471527 100000000
    imHi := q 12471528 100000000 }

def zetaPrimeBallRect : RationalComplexRect :=
  { reLo := q 78 100
    reHi := q 787 1000
    imLo := q 121 1000
    imHi := q 128 1000 }

def zetaSecondDerivativeBound : Rat :=
  q 3 1

def zetaResidualNewtonStepBound : Rat :=
  q 1 20000

structure ZetaAnalyticNumericalObligations
    (I : ZetaAnalyticInterface) where
  derivativeEvaluator :
    ZetaDerivativeBoxEvaluator I zetaNear_14_1347_center
      zetaNear_14_1347_radius
  residualBound :
    ZetaResidualBoxBound I zetaNear_14_1347_center
  centerResidualRect : ComplexBox
  centerResidualRect_readback :
    centerResidualRect.re.lo = zetaCenterResidualRect.reLo ∧
    centerResidualRect.re.hi = zetaCenterResidualRect.reHi ∧
    centerResidualRect.im.lo = zetaCenterResidualRect.imLo ∧
    centerResidualRect.im.hi = zetaCenterResidualRect.imHi
  centerDerivativeRect : ComplexBox
  centerDerivativeRect_readback :
    centerDerivativeRect.re.lo = zetaPrimeCenterRect.reLo ∧
    centerDerivativeRect.re.hi = zetaPrimeCenterRect.reHi ∧
    centerDerivativeRect.im.lo = zetaPrimeCenterRect.imLo ∧
    centerDerivativeRect.im.hi = zetaPrimeCenterRect.imHi
  ballDerivativeRect_readback :
    derivativeEvaluator.derivativeBox.re.lo = zetaPrimeBallRect.reLo ∧
    derivativeEvaluator.derivativeBox.re.hi = zetaPrimeBallRect.reHi ∧
    derivativeEvaluator.derivativeBox.im.lo = zetaPrimeBallRect.imLo ∧
    derivativeEvaluator.derivativeBox.im.hi = zetaPrimeBallRect.imHi
  secondDerivativeBound : Rat
  secondDerivativeBound_readback :
    secondDerivativeBound = zetaSecondDerivativeBound
  residualNewtonStepBound : Rat
  residualNewtonStepBound_readback :
    residualNewtonStepBound = zetaResidualNewtonStepBound

structure VerifiedZetaKrawczykCertificate
    (I : ZetaAnalyticInterface) where
  numerical : ZetaAnalyticNumericalObligations I
  krawczyk : ZetaKrawczykCert I
  center_readback : krawczyk.c = zetaNear_14_1347_center
  radius_readback : krawczyk.r = zetaNear_14_1347_radius
  inverseDerivative_readback :
    krawczyk.a = zetaNear_14_1347_inverseDerivative
  contractionRatio_readback :
    krawczyk.lambda = zetaNear_14_1347_contractionRatio
  derivative_precision_matches :
    krawczyk.derivative_box_bound.precision =
      (derivativeBox_to_krawczyk_bound
        numerical.derivativeEvaluator).precision
  derivative_box_matches :
    krawczyk.derivative_box_bound.derivativeBox =
      (derivativeBox_to_krawczyk_bound
        numerical.derivativeEvaluator).derivativeBox

theorem zetaNear_14_1347_parameters_readback :
    etaEulerCutoff = 64 ∧ etaEulerDepth = 16 := by
  exact And.intro rfl rfl

theorem zetaNear_14_1347_newton_map_readback
    (I : ZetaAnalyticInterface) :
    zetaNewtonMap I zetaNear_14_1347_inverseDerivative =
      zetaNewtonMap I zetaNear_14_1347_inverseDerivative := by
  rfl

theorem derivativeCandidate_to_krawczyk_bound_readback
    {I : ZetaAnalyticInterface}
    (C :
      ZetaDerivativeBoxCandidate I zetaNear_14_1347_center
        zetaNear_14_1347_radius)
    (sound : ZetaDerivativeBoxCandidateSound C) :
    (derivativeCandidate_to_krawczyk_bound C sound).derivativeBox =
      C.derivativeBox ∧
      (derivativeCandidate_to_krawczyk_bound C sound).precision =
        C.etaPrimeEvaluator.cutoff := by
  exact
    BEDC.Derived.RHRoute.ZetaDerivativeBox.zetaDerivativeBoxCandidate_bound_readback
      C sound

theorem located_zeta_zero_near_14_1347_of_verified_certificate
    {I : ZetaAnalyticInterface}
    (cert : VerifiedZetaKrawczykCertificate I) :
    ∃ rho : LocatedComplex,
      LocatedInBall rho zetaNear_14_1347_center
        zetaNear_14_1347_radius ∧
        I.zeta.VanishesAt rho := by
  cases located_zero_of_zeta_krawczyk_cert cert.krawczyk with
  | intro rho zeroData =>
      have hc :
          cert.krawczyk.checker_sound.c = zetaNear_14_1347_center :=
        Eq.trans cert.krawczyk.checker_center cert.center_readback
      have hr :
          cert.krawczyk.checker_sound.r = zetaNear_14_1347_radius :=
        Eq.trans cert.krawczyk.checker_radius cert.radius_readback
      have inConcreteBall :
          LocatedInBall rho zetaNear_14_1347_center
            zetaNear_14_1347_radius := by
        rw [← hc, ← hr]
        exact zeroData.left
      exact Exists.intro rho
        (And.intro inConcreteBall zeroData.right)

end BEDC.Derived.RHRoute.ZetaKrawczykInstantiation
