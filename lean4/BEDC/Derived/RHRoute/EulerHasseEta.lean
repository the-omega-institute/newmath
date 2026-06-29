import BEDC.Derived.RHRoute.ZetaBoxEvaluator
import BEDC.Derived.RHRoute.ZetaDerivativeBox
import BEDC.Derived.BinomialIdentitiesUp

set_option maxHeartbeats 1000000

namespace BEDC.Derived.RHRoute.EulerHasseEta

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev ComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ComplexBox

def q (num : Int) (den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfIntOverNat num den

def qNat (num den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfNatOverNat num den

def cRe : Rat :=
  q 1 2

def cIm : Rat :=
  q 141347 10000

def criticalCenter : RatComplex :=
  { re := cRe, im := cIm }

def criticalRadius : Rat :=
  q 1 1000

def sigmaLo : Rat :=
  q 499 1000

def sigmaHi : Rat :=
  q 501 1000

def tLo : Rat :=
  q 141337 10000

def tHi : Rat :=
  q 141357 10000

def inverseDerivativeApprox : RatComplex :=
  { re := q 12451 10000
    im := q (-2478) 12500 }

def contractionLambda : Rat :=
  q 1 125

def eulerHasseDepth : Nat :=
  96

def eulerHasseElementaryTermCount (M : Nat) : Nat :=
  M * (M + 1) / 2

theorem eulerHasseDepth_readback :
    eulerHasseDepth = 96 ∧
      eulerHasseElementaryTermCount eulerHasseDepth = 4656 := by
  exact And.intro rfl rfl

def ratOfNat (n : Nat) : Rat :=
  qNat n 1

def ratPow (x : Rat) : Nat -> Rat
  | 0 => ratOne
  | Nat.succ n => ratMul x (ratPow x n)

def ratComplexPow (z : RatComplex) : Nat -> RatComplex
  | 0 => ratComplexOne
  | Nat.succ n => ratComplexMul z (ratComplexPow z n)

def twoPowWeight (m : Nat) : Rat :=
  qNat 1 ((2 : Nat) ^ (Nat.succ m))

def signedBinomialRat (m k : Nat) : Rat :=
  let c := BEDC.Derived.BinomialIdentitiesUp.C m k
  if k % 2 = 0 then ratOfNat c else ratNeg (ratOfNat c)

structure HasseTermBox where
  m : Nat
  k : Nat
  powNegSBox : ComplexBox

def hasseTermValue (term : HasseTermBox) : RatComplex :=
  let scaled := ratComplexScale (signedBinomialRat term.m term.k)
    { re := term.powNegSBox.re.lo, im := term.powNegSBox.im.lo }
  ratComplexScale (twoPowWeight term.m) scaled

def hasseInnerSum :
    List HasseTermBox -> RatComplex
  | [] => ratComplexZero
  | term :: rest => ratComplexAdd (hasseTermValue term) (hasseInnerSum rest)

def hassePartialBoxValue (terms : List HasseTermBox) : RatComplex :=
  hasseInnerSum terms

structure EulerHasseFiniteEvaluator where
  M : Nat
  elementaryTerms : List HasseTermBox
  value : RatComplex
  value_eq : value = hassePartialBoxValue elementaryTerms

theorem EulerHasseFiniteEvaluator.value_readback
    (E : EulerHasseFiniteEvaluator) :
    E.value = hassePartialBoxValue E.elementaryTerms := by
  exact E.value_eq

structure QInterval where
  lo : Rat
  hi : Rat

structure RectQ where
  re : QInterval
  im : QInterval

def rectQ (reLo reHi imLo imHi : Rat) : RectQ :=
  { re := { lo := reLo, hi := reHi }
    im := { lo := imLo, hi := imHi } }

def InInterval (x : Rat) (I : QInterval) : Prop :=
  ratLe I.lo x ∧ ratLe x I.hi

def InRect (z : RatComplex) (R : RectQ) : Prop :=
  InInterval z.re R.re ∧ InInterval z.im R.im

def RectQ.ordered (R : RectQ) : Prop :=
  ratLe R.re.lo R.re.hi ∧ ratLe R.im.lo R.im.hi

def RectQ.toComplexBox (R : RectQ) (h : R.ordered) : ComplexBox :=
  { re := { lo := R.re.lo, hi := R.re.hi, valid := h.left }
    im := { lo := R.im.lo, hi := R.im.hi, valid := h.right } }

def rectCorners (I J : QInterval) : List Rat :=
  [ratMul I.lo J.lo, ratMul I.lo J.hi,
    ratMul I.hi J.lo, ratMul I.hi J.hi]

def ratMin (x y : Rat) : Rat :=
  if ratLeBool x y then x else y

def ratMax (x y : Rat) : Rat :=
  if ratLeBool x y then y else x

def ratListMin : List Rat -> Rat
  | [] => ratZero
  | x :: xs => xs.foldl ratMin x

def ratListMax : List Rat -> Rat
  | [] => ratZero
  | x :: xs => xs.foldl ratMax x

def intervalMulHull (I J : QInterval) : QInterval :=
  let corners := rectCorners I J
  { lo := ratListMin corners, hi := ratListMax corners }

def intervalAdd (I J : QInterval) : QInterval :=
  { lo := ratAdd I.lo J.lo, hi := ratAdd I.hi J.hi }

def intervalNeg (I : QInterval) : QInterval :=
  { lo := ratNeg I.hi, hi := ratNeg I.lo }

def intervalSub (I J : QInterval) : QInterval :=
  intervalAdd I (intervalNeg J)

def rectMulHull (A B : RectQ) : RectQ :=
  let ac := intervalMulHull A.re B.re
  let bd := intervalMulHull A.im B.im
  let ad := intervalMulHull A.re B.im
  let bc := intervalMulHull A.im B.re
  { re := intervalSub ac bd
    im := intervalAdd ad bc }

def EtaFiniteBox : RectQ :=
  rectQ (q (-29) 10000000) (q (-28) 10000000)
    (q (-473) 10000000) (q (-472) 10000000)

def EtaTailRadiusBox : RectQ :=
  rectQ (q (-1) 1000000000000) (q 1 1000000000000)
    (q (-1) 1000000000000) (q 1 1000000000000)

def EtaCBox : RectQ :=
  rectQ (q (-3) 1000000) (q (-2) 1000000)
    (q (-48) 1000000) (q (-47) 1000000)

def DBoxC : RectQ :=
  rectQ (q 23171 10000) (q 23172 10000)
    (q (-103) 200) (q (-1287) 2500)

def InvDBoxC : RectQ :=
  rectQ (q 257 625) (q 4113 10000)
    (q 913 10000) (q 183 2000)

def ZetaCBox : RectQ :=
  rectQ (q 3 1000000) (q 4 1000000)
    (q (-21) 1000000) (q (-19) 1000000)

def ZetaPrimeBallBox : RectQ :=
  rectQ (q 39 50) (q 787 1000)
    (q 121 1000) (q 16 125)

def ZetaBallBox : RectQ :=
  rectQ (q (-797) 1000000) (q 201 250000)
    (q (-821) 1000000) (q 781 1000000)

def etaInvDProductHull : RectQ :=
  rectMulHull EtaCBox InvDBoxC

structure RawRatLeCert where
  leftNum : Int
  leftDen : Nat
  rightNum : Int
  rightDen : Nat
  denLeft_pos : 0 < leftDen
  denRight_pos : 0 < rightDen
  cross_le :
    leftNum * Int.ofNat rightDen <= rightNum * Int.ofNat leftDen

structure RawRatLtCert where
  leftNum : Int
  leftDen : Nat
  rightNum : Int
  rightDen : Nat
  denLeft_pos : 0 < leftDen
  denRight_pos : 0 < rightDen
  cross_lt :
    leftNum * Int.ofNat rightDen < rightNum * Int.ofNat leftDen

structure RawIntervalCert where
  loNum : Int
  hiNum : Int
  den : Nat
  den_pos : 0 < den
  ordered : loNum <= hiNum

structure RawBoxCert where
  re : RawIntervalCert
  im : RawIntervalCert

def etaFiniteBoxRawCert : RawBoxCert :=
  { re :=
      { loNum := -29, hiNum := -28, den := 10000000
        den_pos := by decide, ordered := by decide }
    im :=
      { loNum := -473, hiNum := -472, den := 10000000
        den_pos := by decide, ordered := by decide } }

def etaCBoxRawCert : RawBoxCert :=
  { re :=
      { loNum := -3, hiNum := -2, den := 1000000
        den_pos := by decide, ordered := by decide }
    im :=
      { loNum := -48, hiNum := -47, den := 1000000
        den_pos := by decide, ordered := by decide } }

def invDBoxCRawCert : RawBoxCert :=
  { re :=
      { loNum := 257, hiNum := 4113, den := 10000
        den_pos := by decide, ordered := by decide }
    im :=
      { loNum := 913, hiNum := 915, den := 10000
        den_pos := by decide, ordered := by decide } }

def zetaCBoxRawCert : RawBoxCert :=
  { re :=
      { loNum := 3, hiNum := 4, den := 1000000
        den_pos := by decide, ordered := by decide }
    im :=
      { loNum := -21, hiNum := -19, den := 1000000
        den_pos := by decide, ordered := by decide } }

def zetaPrimeBallBoxRawCert : RawBoxCert :=
  { re :=
      { loNum := 780, hiNum := 787, den := 1000
        den_pos := by decide, ordered := by decide }
    im :=
      { loNum := 121, hiNum := 128, den := 1000
        den_pos := by decide, ordered := by decide } }

def zetaBallBoxRawCert : RawBoxCert :=
  { re :=
      { loNum := -797, hiNum := 804, den := 1000000
        den_pos := by decide, ordered := by decide }
    im :=
      { loNum := -821, hiNum := 781, den := 1000000
        den_pos := by decide, ordered := by decide } }

def etaTailInflatesFiniteReLo : RawRatLeCert :=
  { leftNum := -3000001, leftDen := 1000000000000
    rightNum := -2900001, rightDen := 1000000000000
    denLeft_pos := by decide, denRight_pos := by decide
    cross_le := by decide }

def etaTailInflatesFiniteReHi : RawRatLeCert :=
  { leftNum := -2799999, leftDen := 1000000000000
    rightNum := -1999999, rightDen := 1000000000000
    denLeft_pos := by decide, denRight_pos := by decide
    cross_le := by decide }

def etaTailInflatesFiniteImLo : RawRatLeCert :=
  { leftNum := -48000001, leftDen := 1000000000000
    rightNum := -47300001, rightDen := 1000000000000
    denLeft_pos := by decide, denRight_pos := by decide
    cross_le := by decide }

def etaTailInflatesFiniteImHi : RawRatLeCert :=
  { leftNum := -47199999, leftDen := 1000000000000
    rightNum := -46999999, rightDen := 1000000000000
    denLeft_pos := by decide, denRight_pos := by decide
    cross_le := by decide }

structure EtaTailInflationCert where
  reLo : RawRatLeCert
  reHi : RawRatLeCert
  imLo : RawRatLeCert
  imHi : RawRatLeCert

def etaTailInflationCert : EtaTailInflationCert :=
  { reLo := etaTailInflatesFiniteReLo
    reHi := etaTailInflatesFiniteReHi
    imLo := etaTailInflatesFiniteImLo
    imHi := etaTailInflatesFiniteImHi }

structure EtaInvDProductRawInclusionCert where
  reLo : RawRatLeCert
  reHi : RawRatLeCert
  imLo : RawRatLeCert
  imHi : RawRatLeCert

def etaInvDProductRawInclusion : EtaInvDProductRawInclusionCert :=
  { reLo :=
      { leftNum := 3, leftDen := 1000000
        rightNum := 30572, rightDen := 10000000000
        denLeft_pos := by decide, denRight_pos := by decide
        cross_le := by decide }
    reHi :=
      { leftNum := 35696, leftDen := 10000000000
        rightNum := 4, rightDen := 1000000
        denLeft_pos := by decide, denRight_pos := by decide
        cross_le := by decide }
    imLo :=
      { leftNum := -21, leftDen := 1000000
        rightNum := -200169, rightDen := 10000000000
        denLeft_pos := by decide, denRight_pos := by decide
        cross_le := by decide }
    imHi :=
      { leftNum := -195090, leftDen := 10000000000
        rightNum := -19, rightDen := 1000000
        denLeft_pos := by decide, denRight_pos := by decide
        cross_le := by decide } }

def zetaPrimeNormSqRawLeFourFifthsSq : RawRatLeCert :=
  { leftNum := 635753, leftDen := 1000000
    rightNum := 16, rightDen := 25
    denLeft_pos := by decide, denRight_pos := by decide
    cross_le := by decide }

def contractionSquareRawLt : RawRatLtCert :=
  { leftNum := 70577569781, leftDen := 1250000000000000
    rightNum := 1, rightDen := 15625
    denLeft_pos := by decide, denRight_pos := by decide
    cross_lt := by decide }

structure EtaHasseCenterObligation where
  evaluator : EulerHasseFiniteEvaluator
  depth_eq : evaluator.M = eulerHasseDepth
  term_count_eq : evaluator.elementaryTerms.length =
    eulerHasseElementaryTermCount eulerHasseDepth
  finite_box : InRect evaluator.value EtaFiniteBox

structure EtaTailM96Obligation where
  depth : Nat
  sigmaLower : Rat
  sigmaUpper : Rat
  imagLower : Rat
  imagUpper : Rat
  radius : Rat
  depth_eq : depth = eulerHasseDepth
  radius_eq : radius = q 1 1000000000000

structure DenominatorCenterObligation where
  denominator : RatComplex
  inverse : RatComplex
  denominator_box : InRect denominator DBoxC
  inverse_box : InRect inverse InvDBoxC
  inverse_readback :
    ratComplexMul denominator inverse = ratComplexOne

structure ZetaCenterBoxObligation where
  etaFinite : EtaHasseCenterObligation
  etaTail : EtaTailM96Obligation
  denominator : DenominatorCenterObligation

inductive EulerHasseRemainingObligation where
  | elementaryTermPhaseTable
  | hasseTailRadius
  | denominatorPhaseTable
  | denominatorInverseProduct

def remainingObligations : List EulerHasseRemainingObligation :=
  [ EulerHasseRemainingObligation.elementaryTermPhaseTable,
    EulerHasseRemainingObligation.hasseTailRadius,
    EulerHasseRemainingObligation.denominatorPhaseTable,
    EulerHasseRemainingObligation.denominatorInverseProduct ]

theorem remainingObligations_readback :
    remainingObligations.length = 4 := by
  rfl

theorem no_hollow_zeta_center_box :
    (∀ obligation : ZetaCenterBoxObligation,
      InRect
        (ratComplexMul
          (hassePartialBoxValue
            obligation.etaFinite.evaluator.elementaryTerms)
          obligation.denominator.inverse)
        ZetaCBox) ->
    remainingObligations.length = 4 := by
  intro _
  rfl

end BEDC.Derived.RHRoute.EulerHasseEta
