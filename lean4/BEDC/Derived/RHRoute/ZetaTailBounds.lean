import BEDC.Derived.RHRoute.ZetaDerivativeBox

namespace BEDC.Derived.RHRoute.ZetaTailBounds

open BEDC.Derived.RationalUp

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

def q (num : Int) (den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfIntOverNat num den

def qNat (num den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfNatOverNat num den

structure RawQInterval where
  lo : Rat
  hi : Rat

structure RawComplexBox where
  re : RawQInterval
  im : RawQInterval

structure CriticalBallData where
  center : RatComplex
  radius : Rat
  sigmaLower : Rat
  sigmaLowerInv : Rat
  sigmaLowerInvSq : Rat
  imagAbsUpper : Rat

def firstZeroCriticalBall : CriticalBallData :=
  { center := { re := q 1 2, im := q 141347 10000 }
    radius := q 1 1000
    sigmaLower := q 499 1000
    sigmaLowerInv := q 1000 499
    sigmaLowerInvSq := q 1000000 249001
    imagAbsUpper := q 141357 10000 }

inductive LogBoundRoute where
  | atanhSeries
  | namedInteger

structure RationalLogBounds where
  n : Nat
  lo : Rat
  hi : Rat
  lowerRoute : LogBoundRoute
  upperRoute : LogBoundRoute

def logEightBounds : RationalLogBounds :=
  { n := 8
    lo := q 207 100
    hi := q 21 10
    lowerRoute := LogBoundRoute.atanhSeries
    upperRoute := LogBoundRoute.atanhSeries }

structure PowDecayCertificate where
  N : Nat
  p : Nat
  qDen : Nat
  majorant : Rat
  checkProduct : Rat

def ratPow (x : Rat) : Nat -> Rat
  | 0 => ratOne
  | Nat.succ n => ratMul x (ratPow x n)

def natPowRat (n k : Nat) : Rat :=
  qNat (n ^ k) 1

def powDecayCheckProduct
    (N p qDen : Nat) (majorant : Rat) : Rat :=
  ratMul (ratPow majorant qDen) (natPowRat N p)

def criticalPowDecayCertificate : PowDecayCertificate :=
  { N := 8
    p := 499
    qDen := 1000
    majorant := q 1 1
    checkProduct := powDecayCheckProduct 8 499 1000 (q 1 1) }

structure EtaPrimeMonotoneThreshold where
  startN : Nat
  sigmaLower : Rat
  logLower : Rat
  productLower : Rat
  target : Rat

def criticalEtaPrimeMonotoneThreshold : EtaPrimeMonotoneThreshold :=
  { startN := 8
    sigmaLower := firstZeroCriticalBall.sigmaLower
    logLower := logEightBounds.lo
    productLower :=
      ratMul firstZeroCriticalBall.sigmaLower logEightBounds.lo
    target := ratOne }

structure TailParameters where
  startN : Nat
  powMajorant : Rat
  logUpper : Rat
  sigmaLower : Rat
  sigmaLowerInv : Rat
  sigmaLowerInvSq : Rat
  imagAbsUpper : Rat

def criticalTailParameters : TailParameters :=
  { startN := 8
    powMajorant := criticalPowDecayCertificate.majorant
    logUpper := logEightBounds.hi
    sigmaLower := firstZeroCriticalBall.sigmaLower
    sigmaLowerInv := firstZeroCriticalBall.sigmaLowerInv
    sigmaLowerInvSq := firstZeroCriticalBall.sigmaLowerInvSq
    imagAbsUpper := firstZeroCriticalBall.imagAbsUpper }

def etaTailRadius (p : TailParameters) : Rat :=
  ratMul p.powMajorant
    (ratAdd ratOne (ratMul p.imagAbsUpper p.sigmaLowerInv))

def etaTailRatWithInv (_N : Nat) (T P sigmaInv : Rat) : Rat :=
  ratMul P (ratAdd ratOne (ratMul T sigmaInv))

def etaPrimeLeibnizRadius (p : TailParameters) : Rat :=
  ratMul p.powMajorant p.logUpper

def etaPrimePhaseVariationRadius (p : TailParameters) : Rat :=
  ratMul p.powMajorant
    (ratMul p.imagAbsUpper
      (ratAdd (ratMul p.logUpper p.sigmaLowerInv)
        p.sigmaLowerInvSq))

def etaPrimeTailRadius (p : TailParameters) : Rat :=
  ratAdd (etaPrimeLeibnizRadius p)
    (etaPrimePhaseVariationRadius p)

def etaPrimeTailRatWithInv
    (_N : Nat) (T P L sigmaInv sigmaInvSq : Rat) : Rat :=
  ratMul P
    (ratAdd L
      (ratMul T (ratAdd (ratMul L sigmaInv) sigmaInvSq)))

def etaPrimeTailSplitRatWithInv
    (_N : Nat) (T P L sigmaInv sigmaInvSq : Rat) : Rat :=
  ratAdd (ratMul P L)
    (ratMul P
      (ratMul T (ratAdd (ratMul L sigmaInv) sigmaInvSq)))

theorem etaPrimeTailRadius_decomposes
    (p : TailParameters) :
    etaPrimeTailRadius p =
      ratAdd (etaPrimeLeibnizRadius p)
        (etaPrimePhaseVariationRadius p) := by
  rfl

theorem etaTailRadius_readback
    (p : TailParameters) :
    etaTailRadius p =
      ratMul p.powMajorant
        (ratAdd ratOne (ratMul p.imagAbsUpper p.sigmaLowerInv)) := by
  rfl

theorem etaPrimePhaseVariationRadius_readback
    (p : TailParameters) :
    etaPrimePhaseVariationRadius p =
      ratMul p.powMajorant
        (ratMul p.imagAbsUpper
          (ratAdd (ratMul p.logUpper p.sigmaLowerInv)
            p.sigmaLowerInvSq)) := by
  rfl

theorem etaTailRadius_formula_readback
    (p : TailParameters) :
    etaTailRadius p =
      etaTailRatWithInv p.startN p.imagAbsUpper p.powMajorant
        p.sigmaLowerInv := by
  rfl

theorem etaPrimeTailSplitRatWithInv_readback
    (p : TailParameters) :
    etaPrimeTailRadius p =
      etaPrimeTailSplitRatWithInv p.startN p.imagAbsUpper
        p.powMajorant p.logUpper p.sigmaLowerInv
        p.sigmaLowerInvSq := by
  rfl

theorem etaPrimeTailRatWithInv_formula_readback
    (p : TailParameters) :
    etaPrimeTailRatWithInv p.startN p.imagAbsUpper
        p.powMajorant p.logUpper p.sigmaLowerInv
        p.sigmaLowerInvSq =
      ratMul p.powMajorant
        (ratAdd p.logUpper
          (ratMul p.imagAbsUpper
            (ratAdd (ratMul p.logUpper p.sigmaLowerInv)
              p.sigmaLowerInvSq))) := by
  rfl

structure NatPowNegSBox where
  n : Nat
  sigmaLower : Rat
  logBounds : RationalLogBounds
  powMajorant : Rat
  phaseBox : RawComplexBox
  valueBox : RawComplexBox

structure EtaTailEnclosure where
  ball : CriticalBallData
  logTail : RationalLogBounds
  powDecay : PowDecayCertificate
  threshold : EtaPrimeMonotoneThreshold
  parameters : TailParameters
  etaRadius : Rat
  etaPrimeRadius : Rat
  etaRadius_eq : etaRadius = etaTailRadius parameters
  etaPrimeRadius_eq : etaPrimeRadius = etaPrimeTailRadius parameters

def criticalEtaTailEnclosure : EtaTailEnclosure :=
  { ball := firstZeroCriticalBall
    logTail := logEightBounds
    powDecay := criticalPowDecayCertificate
    threshold := criticalEtaPrimeMonotoneThreshold
    parameters := criticalTailParameters
    etaRadius := etaTailRadius criticalTailParameters
    etaPrimeRadius := etaPrimeTailRadius criticalTailParameters
    etaRadius_eq := rfl
    etaPrimeRadius_eq := rfl }

theorem firstZeroCriticalBall_readback :
    firstZeroCriticalBall.center.re = q 1 2 ∧
      firstZeroCriticalBall.center.im = q 141347 10000 ∧
      firstZeroCriticalBall.radius = q 1 1000 ∧
      firstZeroCriticalBall.sigmaLower = q 499 1000 ∧
      firstZeroCriticalBall.imagAbsUpper = q 141357 10000 := by
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl
        (And.intro rfl rfl)))

theorem logEightBounds_readback :
    logEightBounds.n = 8 ∧
      logEightBounds.lo = q 207 100 ∧
      logEightBounds.hi = q 21 10 := by
  exact And.intro rfl (And.intro rfl rfl)

theorem criticalEtaPrimeMonotoneThreshold_readback :
    criticalEtaPrimeMonotoneThreshold.startN = 8 ∧
      criticalEtaPrimeMonotoneThreshold.sigmaLower =
        firstZeroCriticalBall.sigmaLower ∧
      criticalEtaPrimeMonotoneThreshold.logLower = logEightBounds.lo ∧
      criticalEtaPrimeMonotoneThreshold.productLower =
        ratMul firstZeroCriticalBall.sigmaLower logEightBounds.lo ∧
      criticalEtaPrimeMonotoneThreshold.target = ratOne := by
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl
        (And.intro rfl rfl)))

theorem criticalPowDecayCertificate_readback :
    criticalPowDecayCertificate.N = 8 ∧
      criticalPowDecayCertificate.p = 499 ∧
      criticalPowDecayCertificate.qDen = 1000 ∧
      criticalPowDecayCertificate.majorant = q 1 1 ∧
      criticalPowDecayCertificate.checkProduct =
        powDecayCheckProduct 8 499 1000 (q 1 1) := by
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl
        (And.intro rfl rfl)))

theorem criticalTailParameters_readback :
    criticalTailParameters.startN = 8 ∧
      criticalTailParameters.powMajorant =
        criticalPowDecayCertificate.majorant ∧
      criticalTailParameters.logUpper = logEightBounds.hi ∧
      criticalTailParameters.sigmaLower =
        firstZeroCriticalBall.sigmaLower ∧
      criticalTailParameters.sigmaLowerInv =
        firstZeroCriticalBall.sigmaLowerInv ∧
      criticalTailParameters.sigmaLowerInvSq =
        firstZeroCriticalBall.sigmaLowerInvSq ∧
      criticalTailParameters.imagAbsUpper =
        firstZeroCriticalBall.imagAbsUpper := by
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl
        (And.intro rfl
          (And.intro rfl
            (And.intro rfl rfl)))))

theorem criticalEtaTailEnclosure_readback :
    criticalEtaTailEnclosure.ball = firstZeroCriticalBall ∧
      criticalEtaTailEnclosure.logTail = logEightBounds ∧
      criticalEtaTailEnclosure.powDecay = criticalPowDecayCertificate ∧
      criticalEtaTailEnclosure.threshold =
        criticalEtaPrimeMonotoneThreshold ∧
      criticalEtaTailEnclosure.parameters = criticalTailParameters ∧
      criticalEtaTailEnclosure.etaRadius =
        etaTailRadius criticalTailParameters ∧
      criticalEtaTailEnclosure.etaPrimeRadius =
        etaPrimeTailRadius criticalTailParameters := by
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl
        (And.intro rfl
          (And.intro rfl
            (And.intro rfl rfl)))))

theorem criticalEtaPrimeRadius_has_phaseVariation :
    criticalEtaTailEnclosure.etaPrimeRadius =
      ratAdd (etaPrimeLeibnizRadius criticalTailParameters)
        (etaPrimePhaseVariationRadius criticalTailParameters) := by
  rfl

end BEDC.Derived.RHRoute.ZetaTailBounds
