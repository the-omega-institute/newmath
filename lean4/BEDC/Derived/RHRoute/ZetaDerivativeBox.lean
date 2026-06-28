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

structure EtaPrimeTailBound where
  cutoff : Nat
  eulerDepth : Nat
  tailBox : ComplexBox
  tailBound : Rat

structure EtaPrimeFiniteEvaluator where
  cutoff : Nat
  eulerDepth : Nat
  finiteTerms : List (Nat × RatComplex × RatComplex)
  finiteValue : RatComplex
  finiteValue_eq : finiteValue = etaPrimeFiniteSum finiteTerms
  tail : EtaPrimeTailBound

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

end BEDC.Derived.RHRoute.ZetaDerivativeBox
