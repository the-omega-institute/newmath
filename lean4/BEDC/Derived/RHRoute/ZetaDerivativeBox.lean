import BEDC.Derived.BernoulliUp
import BEDC.Derived.RHRoute.KrawczykCertificate

namespace BEDC.Derived.RHRoute.ZetaDerivativeBox

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev ComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ComplexBox

abbrev CMap : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.CMap

abbrev CFun : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.CFun

abbrev ZetaAnalyticInterface : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.ZetaAnalyticInterface

abbrev ZetaDerivativeBoxBound
    (I : ZetaAnalyticInterface) (c : RatComplex) (r : Rat) : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.ZetaDerivativeBoxBound I c r

abbrev Ball (c : RatComplex) (r : Rat) :
    BEDC.Derived.RHRoute.KrawczykCertificate.ClosedBall :=
  BEDC.Derived.RHRoute.KrawczykCertificate.Ball c r

def ComplexInBox (z : RatComplex) (box : ComplexBox) : Prop :=
  BEDC.Derived.RHRoute.KrawczykCertificate.ComplexInBox z box

def ratOfIntOverNat (num : Int) (den : Nat) : Rat :=
  match den with
  | 0 => ratZero
  | Nat.succ d =>
      BEDC.Derived.BernoulliUp.rawRatToRat
        { num := num, denMinusOne := d }

def ratOfNatOverNat (num den : Nat) : Rat :=
  ratOfIntOverNat (Int.ofNat num) den

def ratComplexOfRat (q : Rat) : RatComplex :=
  { re := q, im := ratZero }

def ratComplexScaleByRat (q : Rat) (z : RatComplex) : RatComplex :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexScale q z

def etaPrimeTermValue (n : Nat) (logN nPowNegS : RatComplex) :
    RatComplex :=
  let unsigned := ratComplexMul logN nPowNegS
  if n % 2 = 0 then unsigned else
    BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexNeg unsigned

def etaPrimeFiniteSum :
    List (Nat × RatComplex × RatComplex) -> RatComplex
  | [] => ratComplexZero
  | (n, logN, nPowNegS) :: rest =>
      ratComplexAdd (etaPrimeTermValue n logN nPowNegS)
        (etaPrimeFiniteSum rest)

def etaPrimeEulerWeight (k : Nat) : Rat :=
  ratOfNatOverNat 1 ((2 : Nat) ^ (Nat.succ k))

def etaPrimeEulerCorrectionTerm
    (cutoff k : Nat) (delta : RatComplex) : RatComplex :=
  let scaled := ratComplexScaleByRat (etaPrimeEulerWeight k) delta
  if cutoff % 2 = 0 then
    BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexNeg scaled
  else
    scaled

def etaPrimeEulerCorrection
    (cutoff : Nat) : List (Nat × RatComplex) -> RatComplex
  | [] => ratComplexZero
  | (k, delta) :: rest =>
      ratComplexAdd (etaPrimeEulerCorrectionTerm cutoff k delta)
        (etaPrimeEulerCorrection cutoff rest)

def etaPrimeEulerValue
    (cutoff : Nat)
    (finiteTerms : List (Nat × RatComplex × RatComplex))
    (eulerDeltas : List (Nat × RatComplex)) : RatComplex :=
  ratComplexAdd (etaPrimeFiniteSum finiteTerms)
    (etaPrimeEulerCorrection cutoff eulerDeltas)

structure EtaPrimeTailBound where
  cutoff : Nat
  eulerDepth : Nat
  tailBox : ComplexBox
  tailBound : Rat

inductive TailRatExpr where
  | nat (n : Nat)
  | frac (num den : Nat)
  | add (left right : TailRatExpr)
  | mul (left right : TailRatExpr)

def TailRatExpr.prodNatFrom (start : Nat) : Nat -> TailRatExpr
  | 0 => TailRatExpr.nat 1
  | Nat.succ n =>
      TailRatExpr.mul (TailRatExpr.nat start)
        (TailRatExpr.prodNatFrom (Nat.succ start) n)

def TailRatExpr.sum3
    (a b c : TailRatExpr) : TailRatExpr :=
  TailRatExpr.add (TailRatExpr.add a b) c

def TailRatExpr.sum4
    (a b c d : TailRatExpr) : TailRatExpr :=
  TailRatExpr.add (TailRatExpr.sum3 a b c) d

def TailRatExpr.sum6
    (a b c d e f : TailRatExpr) : TailRatExpr :=
  TailRatExpr.add (TailRatExpr.sum4 a b c d)
    (TailRatExpr.add e f)

def etaEulerTailTwoPowFactor : TailRatExpr :=
  TailRatExpr.frac 1 ((2 : Nat) ^ 16)

def etaEulerTailProductP : TailRatExpr :=
  TailRatExpr.prodNatFrom 15 16

def etaEulerTailH : TailRatExpr :=
  TailRatExpr.frac 8 7

def etaEulerTailJ : TailRatExpr :=
  TailRatExpr.frac 4 49

def etaEulerTailInvPow65 (k : Nat) : TailRatExpr :=
  TailRatExpr.frac 1 ((65 : Nat) ^ k)

def etaEulerTailTerm0Majorant : TailRatExpr :=
  TailRatExpr.mul etaEulerTailTwoPowFactor
    (TailRatExpr.mul etaEulerTailProductP
      (TailRatExpr.add
        (etaEulerTailInvPow65 16)
        (TailRatExpr.mul (etaEulerTailInvPow65 15)
          (TailRatExpr.frac 1 15))))

def etaEulerTailTerm1Local : TailRatExpr :=
  TailRatExpr.add (TailRatExpr.nat 5) etaEulerTailH

def etaEulerTailTerm1Integral : TailRatExpr :=
  TailRatExpr.sum3
    (TailRatExpr.frac 5 15)
    (TailRatExpr.frac 1 (15 ^ 2))
    (TailRatExpr.mul etaEulerTailH (TailRatExpr.frac 1 15))

def etaEulerTailTerm1Majorant : TailRatExpr :=
  TailRatExpr.mul etaEulerTailTwoPowFactor
    (TailRatExpr.mul etaEulerTailProductP
      (TailRatExpr.add
        (TailRatExpr.mul (etaEulerTailInvPow65 16)
          etaEulerTailTerm1Local)
        (TailRatExpr.mul (etaEulerTailInvPow65 15)
          etaEulerTailTerm1Integral)))

def etaEulerTailTerm2Local : TailRatExpr :=
  TailRatExpr.sum4
    (TailRatExpr.nat 25)
    (TailRatExpr.mul (TailRatExpr.nat 10) etaEulerTailH)
    (TailRatExpr.mul etaEulerTailH etaEulerTailH)
    etaEulerTailJ

def etaEulerTailTerm2HIntegral : TailRatExpr :=
  TailRatExpr.mul (TailRatExpr.mul (TailRatExpr.nat 2) etaEulerTailH)
    (TailRatExpr.add
      (TailRatExpr.frac 5 15)
      (TailRatExpr.frac 1 (15 ^ 2)))

def etaEulerTailTerm2HJIntegral : TailRatExpr :=
  TailRatExpr.mul
    (TailRatExpr.add
      (TailRatExpr.mul etaEulerTailH etaEulerTailH)
      etaEulerTailJ)
    (TailRatExpr.frac 1 15)

def etaEulerTailTerm2Integral : TailRatExpr :=
  TailRatExpr.sum6
    (TailRatExpr.frac 25 15)
    (TailRatExpr.frac 10 (15 ^ 2))
    (TailRatExpr.frac 2 (15 ^ 3))
    etaEulerTailTerm2HIntegral
    etaEulerTailTerm2HJIntegral
    (TailRatExpr.nat 0)

def etaEulerTailTerm2Majorant : TailRatExpr :=
  TailRatExpr.mul etaEulerTailTwoPowFactor
    (TailRatExpr.mul etaEulerTailProductP
      (TailRatExpr.add
        (TailRatExpr.mul (etaEulerTailInvPow65 16)
          etaEulerTailTerm2Local)
        (TailRatExpr.mul (etaEulerTailInvPow65 15)
          etaEulerTailTerm2Integral)))

def etaEulerTailTerm0CoarseBound : Rat :=
  ratOfNatOverNat 3 1000000000000

def etaPrimeEulerTailCoarseBound : Rat :=
  ratOfNatOverNat 2 100000000000

def etaSecondEulerTailCoarseBound : Rat :=
  ratOfNatOverNat 1 10000000000

structure EtaEulerTailMajorants where
  cutoff : Nat
  eulerDepth : Nat
  rho0Majorant : TailRatExpr
  rho1Majorant : TailRatExpr
  rho2Majorant : TailRatExpr
  rho0CoarseBound : Rat
  rho1CoarseBound : Rat
  rho2CoarseBound : Rat

def gptProEtaEulerTailMajorants : EtaEulerTailMajorants :=
  { cutoff := 64
    eulerDepth := 16
    rho0Majorant := etaEulerTailTerm0Majorant
    rho1Majorant := etaEulerTailTerm1Majorant
    rho2Majorant := etaEulerTailTerm2Majorant
    rho0CoarseBound := etaEulerTailTerm0CoarseBound
    rho1CoarseBound := etaPrimeEulerTailCoarseBound
    rho2CoarseBound := etaSecondEulerTailCoarseBound }

theorem gptProEtaEulerTailMajorants_readback :
    gptProEtaEulerTailMajorants.cutoff = 64 ∧
      gptProEtaEulerTailMajorants.eulerDepth = 16 ∧
      gptProEtaEulerTailMajorants.rho1CoarseBound =
        ratOfNatOverNat 2 100000000000 := by
  exact And.intro rfl (And.intro rfl rfl)

structure EtaPrimeTailSoundnessObligation where
  majorants : EtaEulerTailMajorants
  tail : EtaPrimeTailBound
  statement : Prop

def etaPrimeTailSoundnessStatement
    (majorants : EtaEulerTailMajorants)
    (tail : EtaPrimeTailBound) : Prop :=
  majorants.cutoff = tail.cutoff ∧
    majorants.eulerDepth = tail.eulerDepth ∧
    tail.tailBound = majorants.rho1CoarseBound

def etaPrimeTailSoundnessObligation
    (tail : EtaPrimeTailBound) : EtaPrimeTailSoundnessObligation :=
  { majorants := gptProEtaEulerTailMajorants
    tail := tail
    statement :=
      etaPrimeTailSoundnessStatement gptProEtaEulerTailMajorants tail }

structure EtaPrimeFiniteEvaluator where
  cutoff : Nat
  eulerDepth : Nat
  finiteTerms : List (Nat × RatComplex × RatComplex)
  finiteValue : RatComplex
  finiteValue_eq : finiteValue = etaPrimeFiniteSum finiteTerms
  tail : EtaPrimeTailBound

structure EtaPrimeEulerEvaluator extends EtaPrimeFiniteEvaluator where
  eulerDeltas : List (Nat × RatComplex)
  correctionValue : RatComplex
  correctionValue_eq :
    correctionValue = etaPrimeEulerCorrection cutoff eulerDeltas
  etaPrimeValue : RatComplex
  etaPrimeValue_eq :
    etaPrimeValue = ratComplexAdd finiteValue correctionValue
  tailObligation : EtaPrimeTailSoundnessObligation

theorem etaPrimeEulerEvaluator_value_readback
    (E : EtaPrimeEulerEvaluator) :
    E.etaPrimeValue =
      ratComplexAdd (etaPrimeFiniteSum E.finiteTerms)
        (etaPrimeEulerCorrection E.cutoff E.eulerDeltas) := by
  rw [E.etaPrimeValue_eq, E.finiteValue_eq, E.correctionValue_eq]

structure ZetaDerivativeFormulaInput where
  eta : RatComplex
  etaPrime : RatComplex
  d : RatComplex
  u : RatComplex
  logTwo : Rat
  denominatorSqApart :
    ratApart0 (ratComplexNormSq (ratComplexMul d d))

def zetaDerivativeNumerator
    (input : ZetaDerivativeFormulaInput) : RatComplex :=
  ratComplexSub (ratComplexMul input.etaPrime input.d)
    (ratComplexMul input.eta
      (ratComplexScaleByRat input.logTwo input.u))

def zetaDerivativeFromEtaData
    (input : ZetaDerivativeFormulaInput) : RatComplex :=
  ratComplexDivApart (zetaDerivativeNumerator input)
    (ratComplexMul input.d input.d) input.denominatorSqApart

theorem zetaDerivativeNumerator_readback
    (input : ZetaDerivativeFormulaInput) :
    zetaDerivativeNumerator input =
      ratComplexSub (ratComplexMul input.etaPrime input.d)
        (ratComplexMul input.eta
          (ratComplexScaleByRat input.logTwo input.u)) := by
  rfl

theorem zetaDerivativeFormula_uses_minus_sign
    (input : ZetaDerivativeFormulaInput) :
    zetaDerivativeFromEtaData input =
      ratComplexDivApart
        (ratComplexSub (ratComplexMul input.etaPrime input.d)
          (ratComplexMul input.eta
            (ratComplexScaleByRat input.logTwo input.u)))
        (ratComplexMul input.d input.d) input.denominatorSqApart := by
  rfl

structure ZetaDerivativeFormulaCertificate
    (I : ZetaAnalyticInterface) where
  etaMap : CMap
  etaPrimeMap : CMap
  twoPowerOneMinusS : CMap
  denominator : CMap
  logTwo : Rat
  denominator_sq_apart :
    ∀ z : RatComplex,
      ratApart0
        (ratComplexNormSq
          (ratComplexMul (denominator z) (denominator z)))
  derivative_readback :
    ∀ z : RatComplex,
      I.zetaDerivative z =
        zetaDerivativeFromEtaData
          { eta := etaMap z
            etaPrime := etaPrimeMap z
            d := denominator z
            u := twoPowerOneMinusS z
            logTwo := logTwo
            denominatorSqApart := denominator_sq_apart z }

def zetaAnalyticInterfaceOfEtaFormula
    (zetaMap : CFun)
    (etaMap etaPrimeMap twoPowerOneMinusS denominator : CMap)
    (logTwo : Rat)
    (denominator_sq_apart :
      ∀ z : RatComplex,
        ratApart0
          (ratComplexNormSq
            (ratComplexMul (denominator z) (denominator z)))) :
    ZetaAnalyticInterface :=
  { zeta := zetaMap
    zetaDerivative :=
      { evalRat := fun z =>
          zetaDerivativeFromEtaData
            { eta := etaMap z
              etaPrime := etaPrimeMap z
              d := denominator z
              u := twoPowerOneMinusS z
              logTwo := logTwo
              denominatorSqApart := denominator_sq_apart z } } }

def zetaDerivativeFormulaCertificateOfEtaData
    (zetaMap : CFun)
    (etaMap etaPrimeMap twoPowerOneMinusS denominator : CMap)
    (logTwo : Rat)
    (denominator_sq_apart :
      ∀ z : RatComplex,
        ratApart0
          (ratComplexNormSq
            (ratComplexMul (denominator z) (denominator z)))) :
    ZetaDerivativeFormulaCertificate
      (zetaAnalyticInterfaceOfEtaFormula zetaMap etaMap etaPrimeMap
        twoPowerOneMinusS denominator logTwo denominator_sq_apart) :=
  { etaMap := etaMap
    etaPrimeMap := etaPrimeMap
    twoPowerOneMinusS := twoPowerOneMinusS
    denominator := denominator
    logTwo := logTwo
    denominator_sq_apart := denominator_sq_apart
    derivative_readback := by
      intro z
      rfl }

theorem zetaAnalyticInterfaceOfEtaFormula_derivative_readback
    (zetaMap : CFun)
    (etaMap etaPrimeMap twoPowerOneMinusS denominator : CMap)
    (logTwo : Rat)
    (denominator_sq_apart :
      ∀ z : RatComplex,
        ratApart0
          (ratComplexNormSq
            (ratComplexMul (denominator z) (denominator z))))
    (z : RatComplex) :
    (zetaAnalyticInterfaceOfEtaFormula zetaMap etaMap etaPrimeMap
      twoPowerOneMinusS denominator logTwo denominator_sq_apart).zetaDerivative z =
      zetaDerivativeFromEtaData
        { eta := etaMap z
          etaPrime := etaPrimeMap z
          d := denominator z
          u := twoPowerOneMinusS z
          logTwo := logTwo
          denominatorSqApart := denominator_sq_apart z } := by
  rfl

structure ZetaDerivativeBoxEvaluator
    (I : ZetaAnalyticInterface) (c : RatComplex) (r : Rat) where
  etaPrimeEvaluator : EtaPrimeFiniteEvaluator
  formula : ZetaDerivativeFormulaCertificate I
  derivativeBox : ComplexBox
  derivative_sound :
    ∀ z : RatComplex, z ∈ Ball c r ->
      ComplexInBox (I.zetaDerivative z) derivativeBox

def derivativeBox_to_krawczyk_bound
    {I : ZetaAnalyticInterface} {c : RatComplex} {r : Rat}
    (E : ZetaDerivativeBoxEvaluator I c r) :
    ZetaDerivativeBoxBound I c r :=
  { precision := E.etaPrimeEvaluator.cutoff
    derivativeBox := E.derivativeBox
    derivative_sound := E.derivative_sound }

structure ZetaDerivativeBoxCandidate
    (I : ZetaAnalyticInterface) (c : RatComplex) (r : Rat) where
  etaPrimeEvaluator : EtaPrimeEulerEvaluator
  formula : ZetaDerivativeFormulaCertificate I
  derivativeBox : ComplexBox

def ZetaDerivativeBoxCandidate.Sound
    {I : ZetaAnalyticInterface} {c : RatComplex} {r : Rat}
    (C : ZetaDerivativeBoxCandidate I c r) : Prop :=
  ∀ z : RatComplex, z ∈ Ball c r ->
    ComplexInBox (I.zetaDerivative z) C.derivativeBox

def ZetaDerivativeBoxCandidate.toEvaluator
    {I : ZetaAnalyticInterface} {c : RatComplex} {r : Rat}
    (C : ZetaDerivativeBoxCandidate I c r) (sound : C.Sound) :
    ZetaDerivativeBoxEvaluator I c r :=
  { etaPrimeEvaluator := C.etaPrimeEvaluator.toEtaPrimeFiniteEvaluator
    formula := C.formula
    derivativeBox := C.derivativeBox
    derivative_sound := sound }

def ZetaDerivativeBoxCandidate.toKrawczykBound
    {I : ZetaAnalyticInterface} {c : RatComplex} {r : Rat}
    (C : ZetaDerivativeBoxCandidate I c r) (sound : C.Sound) :
    ZetaDerivativeBoxBound I c r :=
  derivativeBox_to_krawczyk_bound (C.toEvaluator sound)

theorem zetaDerivativeBoxCandidate_bound_readback
    {I : ZetaAnalyticInterface} {c : RatComplex} {r : Rat}
    (C : ZetaDerivativeBoxCandidate I c r) (sound : C.Sound) :
    (C.toKrawczykBound sound).derivativeBox = C.derivativeBox ∧
      (C.toKrawczykBound sound).precision =
        C.etaPrimeEvaluator.cutoff := by
  exact And.intro rfl rfl

end BEDC.Derived.RHRoute.ZetaDerivativeBox
