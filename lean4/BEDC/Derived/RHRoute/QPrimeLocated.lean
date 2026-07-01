import BEDC.Derived.RHRoute.HalfPlaneEulerProduct
import BEDC.Real.RatNumLogEnclosure
import BEDC.Real.RatNumPhaseBox
import BEDC.Real.RatNumSinCos

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.QPrimeLocated

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.HalfPlaneEulerProduct
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  HalfPlaneEulerProduct.Rat

abbrev RatComplex : Type :=
  HalfPlaneEulerProduct.RatComplex

abbrev QI : Type :=
  BEDC.Real.RatNumPhaseBox.QI

abbrev ComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ComplexBox

def qPoint (x : Rat) : QI :=
  { lo := x, hi := x }

theorem qPoint_ordered (x : Rat) :
    BEDC.Real.RatNumPhaseBox.QI.ordered (qPoint x) :=
  ratLe_refl x

def qIntervalOfQI (I : QI)
    (ordered : BEDC.Real.RatNumPhaseBox.QI.ordered I) :
    BEDC.Derived.RHRoute.ZetaBoxEvaluator.QInterval :=
  { lo := I.lo, hi := I.hi, valid := ordered }

def complexBoxOfQI (re im : QI)
    (re_ordered : BEDC.Real.RatNumPhaseBox.QI.ordered re)
    (im_ordered : BEDC.Real.RatNumPhaseBox.QI.ordered im) :
    ComplexBox :=
  { re := qIntervalOfQI re re_ordered
    im := qIntervalOfQI im im_ordered }

def primeLogLo (p : Nat) : Rat :=
  BEDC.Real.RatNumLogEnclosure.lnLo p
    (BEDC.Real.RatNumLogEnclosure.lnM96 p)

def primeLogHi (p : Nat) (hp1 : 1 ≤ p) : Rat :=
  BEDC.Real.RatNumLogEnclosure.lnHi p
    (BEDC.Real.RatNumLogEnclosure.lnM96 p) hp1

def qPrimeExpInput (p : Nat) (s : RatComplex) : Rat :=
  ratNeg (ratMul s.re (primeLogLo p))

def qPrimePhaseCenter (p : Nat) (s : RatComplex) : Rat :=
  ratMul s.im (primeLogLo p)

def qPrimeAnalyticFormula (p : Nat) (s : RatComplex) : RatComplex :=
  { re := qPrimeExpInput p s
    im := ratNeg (qPrimePhaseCenter p s) }

inductive QPrimeAnalyticBridgeObligation : Type
  | logNatLocated
  | expNegRealLog
  | phaseLogProduct
  | sinCosPhase
  | complexEulerAssembly
  | halfPlaneUnitMajorant
  deriving DecidableEq

structure QPrimeRadialLocated
    (p : Nat) (hp : IsPrime p) (s : RatComplex) where
  exp_input : Rat
  exp_input_eq : exp_input = qPrimeExpInput p s
  radius : Rat
  radius_nonneg : ratLe ratZero radius
  radius_lt_one : ratLt radius ratOne
  unit_majorant : ratLe radius (primeUnitRadius p hp)
  log_enclosure :
    BEDC.Real.RatNumLogEnclosure.SeriesEnclosedFrom
      (fun K =>
        BEDC.Real.RatNumLogEnclosure.atanhFormalSeries
          (BEDC.Real.RatNumLogEnclosure.zOfNat p) K)
      (BEDC.Real.RatNumLogEnclosure.lnM96 p)
      (primeLogLo p)
      (primeLogHi p (Nat.le_of_lt (prime_nat_gt_one hp)))
  bridge_obligations : List QPrimeAnalyticBridgeObligation
  bridge_obligations_eq :
    bridge_obligations =
      [ QPrimeAnalyticBridgeObligation.logNatLocated,
        QPrimeAnalyticBridgeObligation.expNegRealLog,
        QPrimeAnalyticBridgeObligation.halfPlaneUnitMajorant ]

structure QPrimePhaseLocated (p : Nat) (s : RatComplex) where
  phase : Rat
  phase_eq : phase = qPrimePhaseCenter p s
  cos : QI
  sin : QI
  cos_ordered : BEDC.Real.RatNumPhaseBox.QI.ordered cos
  sin_ordered : BEDC.Real.RatNumPhaseBox.QI.ordered sin
  bridge_obligations : List QPrimeAnalyticBridgeObligation
  bridge_obligations_eq :
    bridge_obligations =
      [ QPrimeAnalyticBridgeObligation.phaseLogProduct,
        QPrimeAnalyticBridgeObligation.sinCosPhase ]

def qPrimeReQI {p : Nat} {hp : IsPrime p} {s : RatComplex}
    (radial : QPrimeRadialLocated p hp s)
    (phase : QPrimePhaseLocated p s) : QI :=
  BEDC.Real.RatNumPhaseBox.QI.mul
    (qPoint radial.radius) phase.cos

def qPrimeImQI {p : Nat} {hp : IsPrime p} {s : RatComplex}
    (radial : QPrimeRadialLocated p hp s)
    (phase : QPrimePhaseLocated p s) : QI :=
  BEDC.Real.RatNumPhaseBox.QI.neg
    (BEDC.Real.RatNumPhaseBox.QI.mul
      (qPoint radial.radius) phase.sin)

theorem qPrimeReQI_ordered {p : Nat} {hp : IsPrime p} {s : RatComplex}
    (radial : QPrimeRadialLocated p hp s)
    (phase : QPrimePhaseLocated p s) :
    BEDC.Real.RatNumPhaseBox.QI.ordered
      (qPrimeReQI radial phase) :=
  BEDC.Real.RatNumPhaseBox.QI.mul_ordered
    (qPoint radial.radius) phase.cos

theorem qPrimeImQI_ordered {p : Nat} {hp : IsPrime p} {s : RatComplex}
    (radial : QPrimeRadialLocated p hp s)
    (phase : QPrimePhaseLocated p s) :
    BEDC.Real.RatNumPhaseBox.QI.ordered
      (qPrimeImQI radial phase) :=
  BEDC.Real.RatNumPhaseBox.QI.neg_ordered
    (BEDC.Real.RatNumPhaseBox.QI.mul_ordered
      (qPoint radial.radius) phase.sin)

def qPrimeBox {p : Nat} {hp : IsPrime p} {s : RatComplex}
    (radial : QPrimeRadialLocated p hp s)
    (phase : QPrimePhaseLocated p s) : ComplexBox :=
  complexBoxOfQI (qPrimeReQI radial phase) (qPrimeImQI radial phase)
    (qPrimeReQI_ordered radial phase)
    (qPrimeImQI_ordered radial phase)

def qPrimeEnvelopeOfRadius
    (p : Nat) (s : RatComplex) (radius : Rat)
    (radius_nonneg : ratLe ratZero radius) :
    LocatedComplexMagnitudeEnvelope :=
  { prime := p
    point := s
    absUB := radius
    abs_nonneg := radius_nonneg }

structure QPrimeLocated
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) where
  radial : QPrimeRadialLocated p hp s
  phase : QPrimePhaseLocated p s
  value_box : ComplexBox
  value_box_eq : value_box = qPrimeBox radial phase
  envelope : LocatedComplexMagnitudeEnvelope
  envelope_eq :
    envelope =
      qPrimeEnvelopeOfRadius p s radial.radius radial.radius_nonneg
  formula : RatComplex
  formula_eq : formula = qPrimeAnalyticFormula p s
  radius_contracts : LocalSchurContractive p hp s h
  abs_lt_one : ratLt envelope.absUB ratOne

def assembleQPrimeLocated
    {p : Nat} {hp : IsPrime p} {s : RatComplex} {h : HP1WitnessRat s}
    (radial : QPrimeRadialLocated p hp s)
    (phase : QPrimePhaseLocated p s) :
    QPrimeLocated p hp s h :=
  { radial := radial
    phase := phase
    value_box := qPrimeBox radial phase
    value_box_eq := rfl
    envelope :=
      qPrimeEnvelopeOfRadius p s radial.radius radial.radius_nonneg
    envelope_eq := rfl
    formula := qPrimeAnalyticFormula p s
    formula_eq := rfl
    radius_contracts := qPrime_localSchurContractive p hp s h
    abs_lt_one := radial.radius_lt_one }

def qPrimeLocatedAbs {p : Nat} {hp : IsPrime p} {s : RatComplex}
    {h : HP1WitnessRat s} (located : QPrimeLocated p hp s h) : Rat :=
  located.envelope.absUB

theorem qPrimeLocated_abs_eq
    {p : Nat} {hp : IsPrime p} {s : RatComplex} {h : HP1WitnessRat s}
    (located : QPrimeLocated p hp s h) :
    qPrimeLocatedAbs located = located.radial.radius := by
  unfold qPrimeLocatedAbs
  rw [located.envelope_eq]
  rfl

theorem qPrimeLocated_matches_abs_le
    {p : Nat} {hp : IsPrime p} {s : RatComplex} {h : HP1WitnessRat s}
    (located : QPrimeLocated p hp s h) :
    ratLe (qPrimeLocatedAbs located)
      (qPrimeSymbolicUnitEnvelope p hp s h).absUB := by
  rw [qPrimeLocated_abs_eq located]
  change ratLe located.radial.radius (primeUnitRadius p hp)
  exact located.radial.unit_majorant

theorem qPrimeLocated_matches_localSchur
    {p : Nat} {hp : IsPrime p} {s : RatComplex} {h : HP1WitnessRat s}
    (located : QPrimeLocated p hp s h) :
    ratLe (qPrimeLocatedAbs located)
      (qPrime_localSchurContractive p hp s h).radius := by
  exact qPrimeLocated_matches_abs_le located

def qPrime_located
    {p : Nat} {hp : IsPrime p} {s : RatComplex} {h : HP1WitnessRat s}
    (radial : QPrimeRadialLocated p hp s)
    (phase : QPrimePhaseLocated p s) :
    QPrimeLocated p hp s h :=
  assembleQPrimeLocated radial phase

structure NPowNegLocated (n : Nat) (s : RatComplex)
    (hpos : 0 < n) where
  value_box : ComplexBox
  source_prime :
    ∀ p : Nat, n = p -> (hp : IsPrime p) -> (h : HP1WitnessRat s) ->
      QPrimeLocated p hp s h
  bridge_obligations : List QPrimeAnalyticBridgeObligation
  bridge_obligations_eq :
    bridge_obligations =
      [ QPrimeAnalyticBridgeObligation.logNatLocated,
        QPrimeAnalyticBridgeObligation.expNegRealLog,
        QPrimeAnalyticBridgeObligation.phaseLogProduct,
        QPrimeAnalyticBridgeObligation.sinCosPhase,
        QPrimeAnalyticBridgeObligation.complexEulerAssembly ]

def nPowNegLocatedOfPrime
    {p : Nat} {hp : IsPrime p} {s : RatComplex} {h : HP1WitnessRat s}
    (located : QPrimeLocated p hp s h) :
    NPowNegLocated p s (prime_nat_pos hp) :=
  { value_box := located.value_box
    source_prime := by
      intro p' hpEq hp' h'
      cases hpEq
      exact assembleQPrimeLocated located.radial located.phase
    bridge_obligations :=
      [ QPrimeAnalyticBridgeObligation.logNatLocated,
        QPrimeAnalyticBridgeObligation.expNegRealLog,
        QPrimeAnalyticBridgeObligation.phaseLogProduct,
        QPrimeAnalyticBridgeObligation.sinCosPhase,
        QPrimeAnalyticBridgeObligation.complexEulerAssembly ]
    bridge_obligations_eq := rfl }

theorem nPowNegLocatedOfPrime_matches_qPrimeLocated
    {p : Nat} {hp : IsPrime p} {s : RatComplex} {h : HP1WitnessRat s}
    (located : QPrimeLocated p hp s h) :
    (nPowNegLocatedOfPrime located).value_box = located.value_box := by
  rfl

theorem two_isPrime : IsPrime 2 := by
  change NatPrime (BEDC.Derived.IntUp.natToUnary 2)
  exact NatPrime_first_pair.left

def toyQuarter : Rat :=
  BEDC.Real.RatNumPhaseBox.q 1 4 (by decide)

def toyTwoPoint : RatComplex :=
  { re := ratNat 2, im := ratZero }

theorem toyQuarter_pos :
    ratLt ratZero toyQuarter := by
  unfold toyQuarter BEDC.Real.RatNumPhaseBox.q
  exact div_pos
    (BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos (by decide))
    (BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos (by decide))

theorem toyQuarter_nonneg :
    ratLe ratZero toyQuarter :=
  ratLt_to_ratLe toyQuarter_pos

private theorem ratDivApart_antitone_den_pos_local {x a b : Rat}
    (hx : ratLe ratZero x)
    (ha : ratLt ratZero a)
    (hb : ratLt ratZero b)
    (haApart : ratApart0 a)
    (hbApart : ratApart0 b)
    (hab : ratLe a b) :
    ratLe (ratDivApart x b hbApart) (ratDivApart x a haApart) := by
  have leftCancel :
      RatEq (ratMul (ratDivApart x b hbApart) b) x :=
    ratDivApart_mul_cancel_right hbApart
  have rightCancel :
      RatEq (ratMul (ratDivApart x a haApart) a) x :=
    ratDivApart_mul_cancel_right haApart
  have divBNonneg :
      ratLe ratZero (ratDivApart x b hbApart) :=
    ratDivApart_nonneg_of_nonneg_pos hx hb hbApart
  have step :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x b hbApart) b) := by
    exact ratMul_le_mul_nonneg_left hab divBNonneg
  have toX :
      ratLe (ratMul (ratDivApart x b hbApart) a) x :=
    ratLe_of_RatEq_right step leftCancel
  have targetMul :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x a haApart) a) :=
    ratLe_of_RatEq_right toX (RatEq_symm rightCancel)
  exact ratMul_le_cancel_right ha targetMul

theorem toyQuarter_le_primeUnitRadiusTwo :
    ratLe toyQuarter (primeUnitRadius 2 two_isPrime) := by
  unfold toyQuarter BEDC.Real.RatNumPhaseBox.q primeUnitRadius
  exact ratDivApart_antitone_den_pos_local
    (x := ratOne) (a := ratNat 2) (b := ratNat 4)
    BEDC.Real.RatNumLogEnclosure.ratOne_nonneg
    (BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos (by decide))
    (BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos (by decide))
    (ratApart0_of_pos
      (BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos (by decide)))
    (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos (by decide))
    (ratNat_le_of_nat_le (by decide))

theorem toyQuarter_lt_one :
    ratLt toyQuarter ratOne := by
  exact ratLe_lt_trans toyQuarter_le_primeUnitRadiusTwo
    (primeUnitRadius_lt_one two_isPrime)

theorem one_lt_ratNat_two :
    ratLt ratOne (ratNat 2) := by
  change ratLt (ratNat 1) (ratNat 2)
  exact BEDC.Real.RatNumLogEnclosure.ratNat_lt_of_nat_lt
    (Nat.succ_lt_succ Nat.zero_lt_one)

def toyHP1 : HP1WitnessRat toyTwoPoint :=
  { alpha := ratNat 2
    h_alpha_gt_one := one_lt_ratNat_two
    h_re_ge_alpha := ratLe_refl (ratNat 2) }

def toyRadialLocated :
    QPrimeRadialLocated 2 two_isPrime toyTwoPoint :=
  { exp_input := qPrimeExpInput 2 toyTwoPoint
    exp_input_eq := rfl
    radius := toyQuarter
    radius_nonneg := toyQuarter_nonneg
    radius_lt_one := toyQuarter_lt_one
    unit_majorant := toyQuarter_le_primeUnitRadiusTwo
    log_enclosure :=
      BEDC.Real.RatNumLogEnclosure.formal_lnN_enclosure 2
        (BEDC.Real.RatNumLogEnclosure.lnM96 2)
        (by decide)
    bridge_obligations :=
      [ QPrimeAnalyticBridgeObligation.logNatLocated,
        QPrimeAnalyticBridgeObligation.expNegRealLog,
        QPrimeAnalyticBridgeObligation.halfPlaneUnitMajorant ]
    bridge_obligations_eq := rfl }

def toyPhaseLocated :
    QPrimePhaseLocated 2 toyTwoPoint :=
  { phase := qPrimePhaseCenter 2 toyTwoPoint
    phase_eq := rfl
    cos := qPoint ratOne
    sin := qPoint ratZero
    cos_ordered := qPoint_ordered ratOne
    sin_ordered := qPoint_ordered ratZero
    bridge_obligations :=
      [ QPrimeAnalyticBridgeObligation.phaseLogProduct,
        QPrimeAnalyticBridgeObligation.sinCosPhase ]
    bridge_obligations_eq := rfl }

def qPrimeLocatedToyTwoAtTwo :
    QPrimeLocated 2 two_isPrime toyTwoPoint toyHP1 :=
  assembleQPrimeLocated toyRadialLocated toyPhaseLocated

theorem toy_qPrimeLocated_abs_eq_quarter :
    qPrimeLocatedAbs qPrimeLocatedToyTwoAtTwo = toyQuarter := by
  rfl

theorem toy_qPrimeLocated_real_box_lo_eq_quarter :
    qPrimeLocatedToyTwoAtTwo.value_box.re.lo = toyQuarter := by
  rfl

theorem toy_qPrimeLocated_imag_box_ordered :
    ratLe qPrimeLocatedToyTwoAtTwo.value_box.im.lo
      qPrimeLocatedToyTwoAtTwo.value_box.im.hi := by
  exact qPrimeLocatedToyTwoAtTwo.value_box.im.valid

theorem toy_qPrimeLocated_nonzero_radius :
    ratLt ratZero (qPrimeLocatedAbs qPrimeLocatedToyTwoAtTwo) := by
  rw [toy_qPrimeLocated_abs_eq_quarter]
  exact toyQuarter_pos

structure ToyQPrimeLocatedWitness where
  radial : QPrimeRadialLocated 2 two_isPrime toyTwoPoint
  phase : QPrimePhaseLocated 2 toyTwoPoint
  located : QPrimeLocated 2 two_isPrime toyTwoPoint toyHP1
  located_eq : located = assembleQPrimeLocated radial phase
  abs_eq_quarter : qPrimeLocatedAbs located = toyQuarter
  real_lo_eq_quarter : located.value_box.re.lo = toyQuarter
  imag_box_ordered : ratLe located.value_box.im.lo located.value_box.im.hi
  nonzero_radius : ratLt ratZero (qPrimeLocatedAbs located)

def toyQPrimeLocatedWitness : ToyQPrimeLocatedWitness :=
  { radial := toyRadialLocated
    phase := toyPhaseLocated
    located := qPrimeLocatedToyTwoAtTwo
    located_eq := rfl
    abs_eq_quarter := toy_qPrimeLocated_abs_eq_quarter
    real_lo_eq_quarter := toy_qPrimeLocated_real_box_lo_eq_quarter
    imag_box_ordered := toy_qPrimeLocated_imag_box_ordered
    nonzero_radius := toy_qPrimeLocated_nonzero_radius }

end BEDC.Derived.RHRoute.QPrimeLocated
