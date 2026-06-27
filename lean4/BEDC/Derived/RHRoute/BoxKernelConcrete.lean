import BEDC.Derived.LocatedTranscendental
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.RHRoute.BoxKernelConcrete

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (pairLe_of_length_order)
open BEDC.Derived.RationalUp
open BEDC.Derived.LocatedTranscendental
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev Rat : Type :=
  RatNum

def natOneHist : BHist :=
  BEDC.Derived.PadicUp.NatOne

def concreteNatRat (n : Nat) : Rat :=
  BEDC.Derived.LocatedTranscendental.natRat n

def concreteUnitFraction (n : Nat) : Rat :=
  BEDC.Derived.LocatedTranscendental.unitFraction n

def halfRat : Rat :=
  concreteUnitFraction 1

def singletonInterval (q : Rat) : QInterval :=
  { lo := q
    hi := q
    valid := ratLe_refl q }

def pointBox (z : RatComplex) : ComplexBox :=
  { re := singletonInterval z.re
    im := singletonInterval z.im }

def boxCenter (box : ComplexBox) : RatComplex :=
  { re := box.re.lo
    im := box.im.lo }

def IsPointBox (box : ComplexBox) : Prop :=
  box = pointBox (boxCenter box)

def concreteBoxGauge : BoxGauge :=
  { fits := fun box _k => IsPointBox box
    fits_weaken := by
      intro box hi lo hlo hfit
      exact hfit }

def pointBoxStream (f : Nat -> RatComplex) : BoxStream concreteBoxGauge :=
  { box := fun k => pointBox (f k)
    modulus := fun k => k
    modulus_mono := by
      intro i j hij
      exact hij
    fits_at := by
      intro k n hn
      change IsPointBox (pointBox (f n))
      unfold IsPointBox boxCenter pointBox singletonInterval
      rfl }

def lnNatWindow (n precision : Nat) : RatWindow :=
  lnAroundOneWindow (concreteNatRat n) precision

def lnNatTaylorCenter (n precision : Nat) : Rat :=
  (lnNatWindow n precision).lo

def expRealTaylorCenter (x : Rat) (precision : Nat) : Rat :=
  (expWindow x precision precision).lo

def ratComplexPow (z : RatComplex) : Nat -> RatComplex
  | 0 => ratComplexOne
  | Nat.succ n => ratComplexMul z (ratComplexPow z n)

def ratComplexExpTerm (z : RatComplex) (k : Nat) : RatComplex :=
  ratComplexScale (invFactorialRat k) (ratComplexPow z k)

def ratComplexTaylorSum : List RatComplex -> RatComplex
  | [] => ratComplexZero
  | z :: zs => ratComplexAdd z (ratComplexTaylorSum zs)

def ratComplexExpTermList (z : RatComplex) : Nat -> List RatComplex
  | 0 => [ratComplexOne]
  | Nat.succ n => ratComplexExpTermList z n ++ [ratComplexExpTerm z (Nat.succ n)]

def expComplexTaylorCenter (z : RatComplex) (precision : Nat) : RatComplex :=
  ratComplexTaylorSum (ratComplexExpTermList z precision)

theorem expComplexTaylorCenter_zero (z : RatComplex) :
    expComplexTaylorCenter z 0 = ratComplexOne := by
  unfold expComplexTaylorCenter ratComplexExpTermList ratComplexTaylorSum
  rfl

def negSLogNatCenter (s : RatComplex) (n : Nat) : RatComplex :=
  let logCenter : RatComplex := { re := lnNatTaylorCenter n 0, im := ratZero }
  ratComplexNeg (ratComplexMul s logCenter)

def locatedTaylorComplexApproxKernel (s : RatComplex) :
    ComplexApproxKernel concreteBoxGauge :=
  { lnNat := fun n =>
      pointBoxStream (fun k => { re := lnNatTaylorCenter n k, im := ratZero })
    smallExp := fun z => pointBoxStream (fun k => expComplexTaylorCenter z k)
    rangeReducedExp := fun z => pointBoxStream (fun k => expComplexTaylorCenter z k)
    negSLogNat := fun n =>
      pointBoxStream (fun k => expComplexTaylorCenter (negSLogNatCenter s n) k) }

theorem lnNatWindow_readback (n precision : Nat) :
    lnNatWindow n precision =
      lnAroundOneWindow (concreteNatRat n) precision := by
  rfl

theorem locatedTaylorKernel_negSLogNat_box_readback
    (s : RatComplex) (n precision : Nat) :
    ((locatedTaylorComplexApproxKernel s).negSLogNat n).box precision =
      pointBox (expComplexTaylorCenter (negSLogNatCenter s n) precision) := by
  rfl

theorem locatedTaylorKernel_lnNat_fits (s : RatComplex) (n k : Nat) :
    concreteBoxGauge.fits
      (boxAt ((locatedTaylorComplexApproxKernel s).lnNat n) k) k := by
  exact boxAt_fits ((locatedTaylorComplexApproxKernel s).lnNat n) k

theorem locatedTaylorKernel_negSLogNat_fits (s : RatComplex) (n k : Nat) :
    concreteBoxGauge.fits
      (boxAt ((locatedTaylorComplexApproxKernel s).negSLogNat n) k) k := by
  exact boxAt_fits ((locatedTaylorComplexApproxKernel s).negSLogNat n) k

def concreteBoxAddOp (a b : ComplexBox) : ComplexBox :=
  pointBox (ratComplexAdd (boxCenter a) (boxCenter b))

def concreteBoxAddCertificate : ComplexBoxOpCertificate concreteBoxGauge :=
  { op := concreteBoxAddOp
    work := fun k => k
    work_mono := by
      intro i j hij
      exact hij
    sound := by
      intro k a b ha hb
      change IsPointBox (pointBox (ratComplexAdd (boxCenter a) (boxCenter b)))
      unfold IsPointBox boxCenter pointBox singletonInterval
      rfl }

def pointBoxPairTerm (kernel : ComplexApproxKernel concreteBoxGauge)
    (pairIndex precision : Nat) : ComplexBox :=
  let oddIndex := Nat.succ (pairIndex + pairIndex)
  let evenIndex := Nat.succ oddIndex
  let oddBox := (kernel.negSLogNat oddIndex).box precision
  let evenBox := (kernel.negSLogNat evenIndex).box precision
  pointBox (ratComplexSub (boxCenter oddBox) (boxCenter evenBox))

theorem pointBoxPairTerm_source_eq (s : RatComplex)
    (pairIndex precision : Nat) :
    ∃ reValid :
      (let oddIndex := Nat.succ (pairIndex + pairIndex)
       let evenIndex := Nat.succ oddIndex
       let oddBox := ((locatedTaylorComplexApproxKernel s).negSLogNat oddIndex).box precision
       let evenBox := ((locatedTaylorComplexApproxKernel s).negSLogNat evenIndex).box precision
       ratLe
        (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub oddBox.re.lo evenBox.re.hi)
        (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub oddBox.re.hi evenBox.re.lo)),
    ∃ imValid :
      (let oddIndex := Nat.succ (pairIndex + pairIndex)
       let evenIndex := Nat.succ oddIndex
       let oddBox := ((locatedTaylorComplexApproxKernel s).negSLogNat oddIndex).box precision
       let evenBox := ((locatedTaylorComplexApproxKernel s).negSLogNat evenIndex).box precision
       ratLe
        (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub oddBox.im.lo evenBox.im.hi)
        (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub oddBox.im.hi evenBox.im.lo)),
      pointBoxPairTerm (locatedTaylorComplexApproxKernel s) pairIndex precision =
        etaPairTermBox (locatedTaylorComplexApproxKernel s) pairIndex precision
          reValid imValid := by
  let oddIndex := Nat.succ (pairIndex + pairIndex)
  let evenIndex := Nat.succ oddIndex
  let oddBox := ((locatedTaylorComplexApproxKernel s).negSLogNat oddIndex).box precision
  let evenBox := ((locatedTaylorComplexApproxKernel s).negSLogNat evenIndex).box precision
  have reValid :
      (let oddIndex := Nat.succ (pairIndex + pairIndex)
       let evenIndex := Nat.succ oddIndex
       let oddBox := ((locatedTaylorComplexApproxKernel s).negSLogNat oddIndex).box precision
       let evenBox := ((locatedTaylorComplexApproxKernel s).negSLogNat evenIndex).box precision
       ratLe
        (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub oddBox.re.lo evenBox.re.hi)
        (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub oddBox.re.hi evenBox.re.lo)) := by
    unfold locatedTaylorComplexApproxKernel pointBoxStream pointBox singletonInterval
    exact ratLe_refl _
  have imValid :
      (let oddIndex := Nat.succ (pairIndex + pairIndex)
       let evenIndex := Nat.succ oddIndex
       let oddBox := ((locatedTaylorComplexApproxKernel s).negSLogNat oddIndex).box precision
       let evenBox := ((locatedTaylorComplexApproxKernel s).negSLogNat evenIndex).box precision
       ratLe
        (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub oddBox.im.lo evenBox.im.hi)
        (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub oddBox.im.hi evenBox.im.lo)) := by
    unfold locatedTaylorComplexApproxKernel pointBoxStream pointBox singletonInterval
    exact ratLe_refl _
  exact Exists.intro reValid (Exists.intro imValid rfl)

def concreteEtaPairTermCertificate (s : RatComplex) :
    EtaPairTermCertificate concreteBoxGauge (locatedTaylorComplexApproxKernel s) :=
  { pairTerm := pointBoxPairTerm (locatedTaylorComplexApproxKernel s)
    pairTerm_source := pointBoxPairTerm_source_eq s }

def concreteEtaTailCertificate (s : RatComplex) :
    EtaPairTailCertificate concreteBoxGauge (locatedTaylorComplexApproxKernel s)
      concreteBoxAddCertificate (concreteEtaPairTermCertificate s) :=
  { cutoff := fun k => Nat.succ k
    workPrecision := fun k => k
    cutoff_positive := by
      intro k
      exact Nat.succ_pos k
    work_covers := by
      intro k
      exact Nat.le_refl k
    etaBox := fun k =>
      etaPairPartialSumBox concreteBoxAddCertificate
        (concreteEtaPairTermCertificate s) (Nat.succ k) k
    etaBox_eq := by
      intro k
      rfl
    eta_fits := by
      intro k
      change
        IsPointBox
          (etaPairPartialSumBox concreteBoxAddCertificate
            (concreteEtaPairTermCertificate s) (Nat.succ k) k)
      induction k with
      | zero =>
          unfold etaPairPartialSumBox IsPointBox boxCenter pointBox singletonInterval
          rfl
      | succ k ih =>
          unfold etaPairPartialSumBox
          unfold concreteBoxAddCertificate concreteBoxAddOp
          unfold IsPointBox boxCenter pointBox singletonInterval
          rfl }

theorem intOne_apart : intApart0 intOne := by
  unfold intApart0 intOne intOfNat
  exact Or.inr (hsame_refl natOneHist)

theorem ratOne_apart : ratApart0 ratOne := by
  unfold ratApart0 ratOne intToRat
  exact intOne_apart

theorem halfRat_apart : ratApart0 halfRat := by
  unfold halfRat concreteUnitFraction
  unfold BEDC.Derived.LocatedTranscendental.unitFraction ratApart0
  exact intOne_apart

def halfRat_strictPositive : RatStrictPositive halfRat :=
  { left := rfl
    right := halfRat_apart }

def ratOne_strictPositive : RatStrictPositive ratOne :=
  { left := rfl
    right := ratOne_apart }

theorem halfRat_le_one_sub_halfRat :
    ratLe halfRat (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub ratOne halfRat) := by
  unfold halfRat concreteUnitFraction
  unfold BEDC.Derived.LocatedTranscendental.unitFraction
  unfold BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub ratLe intLe
  apply pairLe_of_length_order
  · exact intToPair_carrier _
  · exact intToPair_carrier _
  decide

def concreteCriticalStripHalf : CriticalStripInput :=
  { re := halfRat
    im := ratZero
    sigmaLower := halfRat
    sigmaUpperGap := halfRat
    imagBound := ratZero
    sigmaLower_pos := halfRat_strictPositive
    sigmaUpperGap_pos := halfRat_strictPositive
    re_lower := ratLe_refl halfRat
    re_upper := halfRat_le_one_sub_halfRat }

def criticalHalfTwoPowerCenter : RatComplex :=
  { re := ratAdd ratOne halfRat
    im := ratZero }

def criticalHalfDenominatorCenter : RatComplex :=
  { re := ratNeg halfRat
    im := ratZero }

theorem criticalHalfDenominator_apart :
    ratApart0 (ratComplexNormSq criticalHalfDenominatorCenter) := by
  unfold criticalHalfDenominatorCenter ratComplexNormSq
  unfold halfRat concreteUnitFraction BEDC.Derived.LocatedTranscendental.unitFraction
  unfold ratApart0 ratAdd ratMul ratNeg ratZero intToRat intOne intZero intOfNat
  exact Or.inr (hsame_refl natOneHist)

def divideBoxBy (denominator : RatComplex)
    (denominator_apart : ratApart0 (ratComplexNormSq denominator))
    (etaBox : ComplexBox) : ComplexBox :=
  pointBox (ratComplexDivApart (boxCenter etaBox) denominator denominator_apart)

def criticalHalfDivisionCertificate :
    ZetaDivisionCertificate concreteBoxGauge criticalHalfDenominatorCenter
      criticalHalfDenominator_apart :=
  { divide := divideBoxBy criticalHalfDenominatorCenter criticalHalfDenominator_apart
    work := fun k => k
    work_mono := by
      intro i j hij
      exact hij
    sound := by
      intro k etaBox hfit
      change
        IsPointBox
          (pointBox
            (ratComplexDivApart (boxCenter etaBox) criticalHalfDenominatorCenter
              criticalHalfDenominator_apart))
      unfold IsPointBox boxCenter pointBox singletonInterval
      rfl
    centerDivides := by
      intro eta
      rfl }

def criticalHalfDenominatorSeparation :
    DenominatorSeparation concreteCriticalStripHalf concreteBoxGauge :=
  { twoPowOneMinusS := pointBoxStream (fun _k => criticalHalfTwoPowerCenter)
    lowerBound := halfRat
    lowerBound_pos := halfRat_strictPositive
    denominatorCenter := criticalHalfDenominatorCenter
    denominator_apart := criticalHalfDenominator_apart
    separation_fits := by
      intro k
      exact boxAt_fits (pointBoxStream (fun _k => criticalHalfTwoPowerCenter)) k }

def concreteDivisionCertificate :
    ZetaDivisionCertificate concreteBoxGauge ratComplexOne
      (by
        unfold ratComplexNormSq ratComplexOne
        exact ratOne_apart) :=
  { divide := divideBoxBy ratComplexOne
      (by
        unfold ratComplexNormSq ratComplexOne
        exact ratOne_apart)
    work := fun k => k
    work_mono := by
      intro i j hij
      exact hij
    sound := by
      intro k etaBox hfit
      change
        IsPointBox
          (pointBox
            (ratComplexDivApart (boxCenter etaBox) ratComplexOne
              (by
                unfold ratComplexNormSq ratComplexOne
                exact ratOne_apart)))
      unfold IsPointBox boxCenter pointBox singletonInterval
      rfl
    centerDivides := by
      intro eta
      rfl }

def criticalStripPoint (s : CriticalStripInput) : RatComplex :=
  { re := s.re
    im := s.im }

def concreteZetaBoxEvaluator :
    ZetaBoxEvaluator concreteBoxGauge concreteCriticalStripHalf :=
  { kernel := locatedTaylorComplexApproxKernel (criticalStripPoint concreteCriticalStripHalf)
    boxAdd := concreteBoxAddCertificate
    etaPairTerm :=
      concreteEtaPairTermCertificate (criticalStripPoint concreteCriticalStripHalf)
    etaTail := concreteEtaTailCertificate (criticalStripPoint concreteCriticalStripHalf)
    denominator := criticalHalfDenominatorSeparation
    division := criticalHalfDivisionCertificate }

def concreteZetaBox (precision : Nat) : ComplexBox :=
  zetaBox concreteZetaBoxEvaluator precision

def concreteZetaPrecisionPacket (precision : Nat) :
    ZetaPrecisionPacket concreteZetaBoxEvaluator precision :=
  { etaPrecision := precision
    etaBox := concreteZetaBoxEvaluator.etaTail.etaBox precision
    eta_fits := concreteZetaBoxEvaluator.etaTail.eta_fits precision
    zetaBox := concreteZetaBox precision
    zetaBox_eq := by
      unfold concreteZetaBox zetaBox
      rfl
    zeta_fits := zetaBox_fits concreteZetaBoxEvaluator precision
    denominator_apart := concreteZetaBoxEvaluator.denominator.denominator_apart }

theorem concreteZetaBox_fits (precision : Nat) :
    concreteBoxGauge.fits (concreteZetaBox precision) precision := by
  exact zetaBox_fits concreteZetaBoxEvaluator precision

theorem concreteZetaPrecisionPacket_fits (precision : Nat) :
    concreteBoxGauge.fits
      (concreteZetaPrecisionPacket precision).zetaBox precision := by
  exact (concreteZetaPrecisionPacket precision).zeta_fits

def concreteCriticalHalfEvaluator :
    ZetaBoxEvaluator concreteBoxGauge concreteCriticalStripHalf :=
  concreteZetaBoxEvaluator

def concreteCriticalHalfZetaBox (precision : Nat) : ComplexBox :=
  concreteZetaBox precision

theorem concreteCriticalHalfZetaBox_readback (precision : Nat) :
    concreteCriticalHalfZetaBox precision =
      concreteZetaBox precision := by
  rfl

def concreteCriticalHalfPrecisionPacket (precision : Nat) :
    ZetaPrecisionPacket concreteCriticalHalfEvaluator precision :=
  concreteZetaPrecisionPacket precision

def rationalTwoOnRealAxis : RatComplex :=
  { re := concreteNatRat 2
    im := ratZero }

def concreteEtaTwoPartialBox (precision : Nat) : ComplexBox :=
  etaPairPartialSumBox concreteBoxAddCertificate
    (concreteEtaPairTermCertificate rationalTwoOnRealAxis) (Nat.succ precision)
    precision

def concreteZetaTwoPartialBox (precision : Nat) : ComplexBox :=
  pointBox
    (ratComplexScale (concreteNatRat 2)
      (boxCenter (concreteEtaTwoPartialBox precision)))

def concreteZetaTwoBox (precision : Nat) : ComplexBox :=
  concreteZetaTwoPartialBox precision

theorem concreteZetaTwoBox_readback (precision : Nat) :
    concreteZetaTwoBox precision =
      concreteZetaTwoPartialBox precision := by
  rfl

theorem concreteCriticalHalfZetaBox_fits (precision : Nat) :
    concreteBoxGauge.fits (concreteCriticalHalfZetaBox precision) precision := by
  exact zetaBox_fits concreteCriticalHalfEvaluator precision

theorem concreteCriticalHalfPacket_fits (precision : Nat) :
    concreteBoxGauge.fits
      (concreteCriticalHalfPrecisionPacket precision).zetaBox precision := by
  exact (concreteCriticalHalfPrecisionPacket precision).zeta_fits

theorem concreteZetaTwoPartialBox_zero_eq :
    concreteZetaTwoPartialBox 0 =
      pointBox
        (ratComplexScale (concreteNatRat 2)
          (boxCenter
            (etaPairPartialSumBox concreteBoxAddCertificate
              (concreteEtaPairTermCertificate rationalTwoOnRealAxis) 1 0))) := by
  rfl

theorem concreteZetaTwoBox_fits (precision : Nat) :
    concreteBoxGauge.fits (concreteZetaTwoBox precision) precision := by
  change
    IsPointBox
      (pointBox
        (ratComplexScale (concreteNatRat 2)
          (boxCenter (concreteEtaTwoPartialBox precision))))
  unfold IsPointBox boxCenter pointBox singletonInterval
  rfl

end BEDC.Derived.RHRoute.BoxKernelConcrete
