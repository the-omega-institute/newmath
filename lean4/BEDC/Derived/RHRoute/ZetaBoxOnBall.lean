import BEDC.Derived.RHRoute.ZetaTailBounds
import BEDC.Derived.RHRoute.ZetaKrawczykInstantiation

namespace BEDC.Derived.RHRoute.ZetaBoxOnBall

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.KrawczykCertificate

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev ComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ComplexBox

abbrev RawQInterval : Type :=
  BEDC.Derived.RHRoute.ZetaTailBounds.RawQInterval

abbrev RawComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaTailBounds.RawComplexBox

abbrev ZetaAnalyticInterface : Type :=
  BEDC.Derived.RHRoute.KrawczykCertificate.ZetaAnalyticInterface

abbrev EtaTailEnclosure : Type :=
  BEDC.Derived.RHRoute.ZetaTailBounds.EtaTailEnclosure

abbrev TailParameters : Type :=
  BEDC.Derived.RHRoute.ZetaTailBounds.TailParameters

def q (num : Int) (den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfIntOverNat num den

def qNat (num den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfNatOverNat num den

def rawInterval (lo hi : Rat) : RawQInterval :=
  { lo := lo, hi := hi }

def rawBox (reLo reHi imLo imHi : Rat) : RawComplexBox :=
  { re := rawInterval reLo reHi
    im := rawInterval imLo imHi }

def rawSymmetricBox (radius : Rat) : RawComplexBox :=
  rawBox (ratNeg radius) radius (ratNeg radius) radius

def rawQIntervalOrdered (I : RawQInterval) : Prop :=
  ratLe I.lo I.hi

def rawComplexBoxOrdered (box : RawComplexBox) : Prop :=
  rawQIntervalOrdered box.re ∧ rawQIntervalOrdered box.im

def rawQIntervalToQInterval
    (I : RawQInterval) (ordered : rawQIntervalOrdered I) :
    BEDC.Derived.RHRoute.ZetaBoxEvaluator.QInterval :=
  { lo := I.lo, hi := I.hi, valid := ordered }

def rawComplexBoxToComplexBox
    (box : RawComplexBox) (ordered : rawComplexBoxOrdered box) :
    ComplexBox :=
  { re := rawQIntervalToQInterval box.re ordered.left
    im := rawQIntervalToQInterval box.im ordered.right }

def criticalCenter : RatComplex :=
  BEDC.Derived.RHRoute.ZetaTailBounds.firstZeroCriticalBall.center

def criticalRadius : Rat :=
  BEDC.Derived.RHRoute.ZetaTailBounds.firstZeroCriticalBall.radius

def criticalBall : ClosedBall :=
  Ball criticalCenter criticalRadius

def etaFiniteCutoffFromTail (tail : EtaTailEnclosure) : Nat :=
  tail.parameters.startN - 1

def etaTailRadiusFor (p : TailParameters) : Rat :=
  BEDC.Derived.RHRoute.ZetaTailBounds.etaTailRadius p

def etaPrimeTailRadiusFor (p : TailParameters) : Rat :=
  BEDC.Derived.RHRoute.ZetaTailBounds.etaPrimeTailRadius p

inductive BallBoxRoute where
  | etaFiniteTailDivision
  | derivativeFormulaTail
  | lipschitzTube

structure EtaBallBoxPlan where
  cutoff : Nat
  tail : EtaTailEnclosure
  finiteValueBox : RawComplexBox
  tailRadius : Rat
  etaBox : RawComplexBox
  route : BallBoxRoute
  cutoff_eq : cutoff = etaFiniteCutoffFromTail tail
  tailRadius_eq : tailRadius = etaTailRadiusFor tail.parameters

structure EtaPrimeBallBoxPlan where
  cutoff : Nat
  tail : EtaTailEnclosure
  finiteValueBox : RawComplexBox
  tailRadius : Rat
  etaPrimeBox : RawComplexBox
  route : BallBoxRoute
  cutoff_eq : cutoff = etaFiniteCutoffFromTail tail
  tailRadius_eq : tailRadius = etaPrimeTailRadiusFor tail.parameters

structure ZetaBallBoxCandidate where
  center : RatComplex
  radius : Rat
  etaPlan : EtaBallBoxPlan
  denominatorBox : RawComplexBox
  zetaBox : RawComplexBox
  route : BallBoxRoute

structure ZetaPrimeBallBoxCandidate where
  center : RatComplex
  radius : Rat
  etaPlan : EtaBallBoxPlan
  etaPrimePlan : EtaPrimeBallBoxPlan
  denominatorBox : RawComplexBox
  twoPowerBox : RawComplexBox
  logTwoBounds : BEDC.Derived.RHRoute.ZetaTailBounds.RationalLogBounds
  zetaPrimeBox : RawComplexBox
  route : BallBoxRoute

def centerResidualRawBox : RawComplexBox :=
  rawBox
    (q 3135 1000000000) (q 3136 1000000000)
    (q (-19694) 1000000000) (q (-19693) 1000000000)

def zetaBallTubeRawBox : RawComplexBox :=
  rawBox
    (q (-1) 1000) (q 1 1000)
    (q (-1) 1000) (q 1 1000)

def zetaPrimeBallRawBox : RawComplexBox :=
  rawBox
    (q 78 100) (q 787 1000)
    (q 121 1000) (q 128 1000)

def criticalDenominatorRawBox : RawComplexBox :=
  rawBox
    (q 237 100) (q 5 2)
    (q (-3) 5) (q (-1) 2)

def criticalTwoPowerRawBox : RawComplexBox :=
  rawBox
    (q (-1319) 1000) (q (-263) 200)
    (q 513 1000) (q 517 1000)

def criticalEtaRawBox : RawComplexBox :=
  rawSymmetricBox (q 1 50)

def criticalEtaPrimeRawBox : RawComplexBox :=
  rawBox
    (q 187 100) (q 189 100)
    (q (-13) 100) (q (-1) 10)

def criticalEtaBallPlan : EtaBallBoxPlan :=
  { cutoff :=
      etaFiniteCutoffFromTail
        BEDC.Derived.RHRoute.ZetaTailBounds.criticalEtaTailEnclosure
    tail := BEDC.Derived.RHRoute.ZetaTailBounds.criticalEtaTailEnclosure
    finiteValueBox := criticalEtaRawBox
    tailRadius :=
      etaTailRadiusFor
        BEDC.Derived.RHRoute.ZetaTailBounds.criticalTailParameters
    etaBox := criticalEtaRawBox
    route := BallBoxRoute.etaFiniteTailDivision
    cutoff_eq := rfl
    tailRadius_eq := rfl }

def criticalEtaPrimeBallPlan : EtaPrimeBallBoxPlan :=
  { cutoff :=
      etaFiniteCutoffFromTail
        BEDC.Derived.RHRoute.ZetaTailBounds.criticalEtaTailEnclosure
    tail := BEDC.Derived.RHRoute.ZetaTailBounds.criticalEtaTailEnclosure
    finiteValueBox := criticalEtaPrimeRawBox
    tailRadius :=
      etaPrimeTailRadiusFor
        BEDC.Derived.RHRoute.ZetaTailBounds.criticalTailParameters
    etaPrimeBox := criticalEtaPrimeRawBox
    route := BallBoxRoute.derivativeFormulaTail
    cutoff_eq := rfl
    tailRadius_eq := rfl }

def criticalZetaBallBoxCandidate : ZetaBallBoxCandidate :=
  { center := criticalCenter
    radius := criticalRadius
    etaPlan := criticalEtaBallPlan
    denominatorBox := criticalDenominatorRawBox
    zetaBox := zetaBallTubeRawBox
    route := BallBoxRoute.etaFiniteTailDivision }

def criticalZetaPrimeBallBoxCandidate : ZetaPrimeBallBoxCandidate :=
  { center := criticalCenter
    radius := criticalRadius
    etaPlan := criticalEtaBallPlan
    etaPrimePlan := criticalEtaPrimeBallPlan
    denominatorBox := criticalDenominatorRawBox
    twoPowerBox := criticalTwoPowerRawBox
    logTwoBounds := BEDC.Derived.RHRoute.ZetaTailBounds.logEightBounds
    zetaPrimeBox := zetaPrimeBallRawBox
    route := BallBoxRoute.derivativeFormulaTail }

structure ZetaBallBoxOrder (candidate : ZetaBallBoxCandidate) where
  residual_ordered : rawComplexBoxOrdered centerResidualRawBox
  zeta_ordered : rawComplexBoxOrdered candidate.zetaBox
  eta_ordered : rawComplexBoxOrdered candidate.etaPlan.etaBox
  denominator_ordered : rawComplexBoxOrdered candidate.denominatorBox

structure ZetaPrimeBallBoxOrder
    (candidate : ZetaPrimeBallBoxCandidate) where
  zetaPrime_ordered : rawComplexBoxOrdered candidate.zetaPrimeBox
  eta_ordered : rawComplexBoxOrdered candidate.etaPlan.etaBox
  etaPrime_ordered :
    rawComplexBoxOrdered candidate.etaPrimePlan.etaPrimeBox
  denominator_ordered : rawComplexBoxOrdered candidate.denominatorBox
  twoPower_ordered : rawComplexBoxOrdered candidate.twoPowerBox

def ZetaBallBoxCandidate.zetaComplexBox
    (candidate : ZetaBallBoxCandidate)
    (order : ZetaBallBoxOrder candidate) : ComplexBox :=
  rawComplexBoxToComplexBox candidate.zetaBox order.zeta_ordered

def ZetaBallBoxCandidate.residualComplexBox
    (_candidate : ZetaBallBoxCandidate)
    (order : ZetaBallBoxOrder _candidate) : ComplexBox :=
  rawComplexBoxToComplexBox centerResidualRawBox order.residual_ordered

def ZetaPrimeBallBoxCandidate.derivativeComplexBox
    (candidate : ZetaPrimeBallBoxCandidate)
    (order : ZetaPrimeBallBoxOrder candidate) : ComplexBox :=
  rawComplexBoxToComplexBox candidate.zetaPrimeBox
    order.zetaPrime_ordered

structure ZetaBallBoxSound
    (I : ZetaAnalyticInterface)
    (candidate : ZetaBallBoxCandidate)
    (order : ZetaBallBoxOrder candidate) where
  zeta_sound :
    ∀ z : RatComplex, z ∈ Ball candidate.center candidate.radius ->
      ComplexInBox (I.zeta z) (candidate.zetaComplexBox order)
  center_sound :
    ComplexInBox (I.zeta candidate.center)
      (candidate.residualComplexBox order)

structure ZetaPrimeBallBoxSound
    (I : ZetaAnalyticInterface)
    (candidate : ZetaPrimeBallBoxCandidate)
    (order : ZetaPrimeBallBoxOrder candidate) where
  derivative_sound :
    ∀ z : RatComplex, z ∈ Ball candidate.center candidate.radius ->
      ComplexInBox (I.zetaDerivative z)
        (candidate.derivativeComplexBox order)

structure ZetaBallAnalyticBounds
    (I : ZetaAnalyticInterface) where
  zetaCandidate : ZetaBallBoxCandidate
  zetaPrimeCandidate : ZetaPrimeBallBoxCandidate
  zetaOrder : ZetaBallBoxOrder zetaCandidate
  zetaPrimeOrder : ZetaPrimeBallBoxOrder zetaPrimeCandidate
  zetaSound : ZetaBallBoxSound I zetaCandidate zetaOrder
  zetaPrimeSound :
    ZetaPrimeBallBoxSound I zetaPrimeCandidate zetaPrimeOrder
  same_center : zetaPrimeCandidate.center = zetaCandidate.center
  same_radius : zetaPrimeCandidate.radius = zetaCandidate.radius

def ZetaBallBoxSound.toResidualBound
    {I : ZetaAnalyticInterface}
    {candidate : ZetaBallBoxCandidate}
    {order : ZetaBallBoxOrder candidate}
    (sound : ZetaBallBoxSound I candidate order) :
    ZetaResidualBoxBound I candidate.center :=
  { precision := candidate.etaPlan.cutoff
    residualBox := candidate.residualComplexBox order
    center_sound := sound.center_sound }

def ZetaPrimeBallBoxSound.toDerivativeBound
    {I : ZetaAnalyticInterface}
    {candidate : ZetaPrimeBallBoxCandidate}
    {order : ZetaPrimeBallBoxOrder candidate}
    (sound : ZetaPrimeBallBoxSound I candidate order) :
    ZetaDerivativeBoxBound I candidate.center candidate.radius :=
  { precision := candidate.etaPrimePlan.cutoff
    derivativeBox := candidate.derivativeComplexBox order
    derivative_sound := sound.derivative_sound }

def ZetaBallAnalyticBounds.residualBound
    {I : ZetaAnalyticInterface} (bounds : ZetaBallAnalyticBounds I) :
    ZetaResidualBoxBound I bounds.zetaCandidate.center :=
  bounds.zetaSound.toResidualBound

def ZetaBallAnalyticBounds.derivativeBound
    {I : ZetaAnalyticInterface} (bounds : ZetaBallAnalyticBounds I) :
    ZetaDerivativeBoxBound I bounds.zetaPrimeCandidate.center
      bounds.zetaPrimeCandidate.radius :=
  bounds.zetaPrimeSound.toDerivativeBound

structure CriticalZetaBallCertificate
    (I : ZetaAnalyticInterface) where
  bounds : ZetaBallAnalyticBounds I
  zetaCandidate_readback :
    bounds.zetaCandidate = criticalZetaBallBoxCandidate
  zetaPrimeCandidate_readback :
    bounds.zetaPrimeCandidate = criticalZetaPrimeBallBoxCandidate

theorem criticalCenter_readback :
    criticalCenter.re = q 1 2 ∧
      criticalCenter.im = q 141347 10000 ∧
      criticalRadius = q 1 1000 := by
  exact And.intro rfl (And.intro rfl rfl)

theorem criticalEtaBallPlan_tail_readback :
    criticalEtaBallPlan.cutoff = 7 ∧
      criticalEtaBallPlan.tailRadius =
        BEDC.Derived.RHRoute.ZetaTailBounds.etaTailRadius
          BEDC.Derived.RHRoute.ZetaTailBounds.criticalTailParameters ∧
      criticalEtaBallPlan.tail.parameters.startN = 8 := by
  exact And.intro rfl (And.intro rfl rfl)

theorem criticalEtaPrimeBallPlan_tail_readback :
    criticalEtaPrimeBallPlan.cutoff = 7 ∧
      criticalEtaPrimeBallPlan.tailRadius =
        BEDC.Derived.RHRoute.ZetaTailBounds.etaPrimeTailRadius
          BEDC.Derived.RHRoute.ZetaTailBounds.criticalTailParameters ∧
      criticalEtaPrimeBallPlan.tail.parameters.startN = 8 := by
  exact And.intro rfl (And.intro rfl rfl)

theorem criticalZetaBallBox_readback :
    criticalZetaBallBoxCandidate.center = criticalCenter ∧
      criticalZetaBallBoxCandidate.radius = criticalRadius ∧
      criticalZetaBallBoxCandidate.zetaBox = zetaBallTubeRawBox ∧
      criticalZetaBallBoxCandidate.etaPlan = criticalEtaBallPlan := by
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl rfl))

theorem criticalZetaPrimeBallBox_readback :
    criticalZetaPrimeBallBoxCandidate.center = criticalCenter ∧
      criticalZetaPrimeBallBoxCandidate.radius = criticalRadius ∧
      criticalZetaPrimeBallBoxCandidate.zetaPrimeBox =
        zetaPrimeBallRawBox ∧
      criticalZetaPrimeBallBoxCandidate.etaPrimePlan =
        criticalEtaPrimeBallPlan := by
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl rfl))

theorem residualBound_from_bounds_readback
    {I : ZetaAnalyticInterface}
    (bounds : ZetaBallAnalyticBounds I) :
    bounds.residualBound.residualBox =
      bounds.zetaCandidate.residualComplexBox bounds.zetaOrder ∧
      bounds.residualBound.precision =
        bounds.zetaCandidate.etaPlan.cutoff := by
  exact And.intro rfl rfl

theorem derivativeBound_from_bounds_readback
    {I : ZetaAnalyticInterface}
    (bounds : ZetaBallAnalyticBounds I) :
    bounds.derivativeBound.derivativeBox =
      bounds.zetaPrimeCandidate.derivativeComplexBox
        bounds.zetaPrimeOrder ∧
      bounds.derivativeBound.precision =
        bounds.zetaPrimeCandidate.etaPrimePlan.cutoff := by
  exact And.intro rfl rfl

end BEDC.Derived.RHRoute.ZetaBoxOnBall
