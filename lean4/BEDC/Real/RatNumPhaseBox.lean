import BEDC.Real.RatNumLogEnclosure
import BEDC.Real.RatNumSinCos

set_option maxHeartbeats 2000000

namespace BEDC.Real.RatNumPhaseBox

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  RatNumKernel.Rat

def q (num : Nat) (den : Nat) (hden : 0 < den) : Rat :=
  ratDivApart (ratNat num) (ratNat den)
    (RatNumLogEnclosure.ratNat_apart0_of_pos hden)

def qInt (num : Int) (den : Nat) : Rat :=
  match num with
  | Int.ofNat n =>
      match den with
      | 0 => ratZero
      | Nat.succ d => q n (Nat.succ d) (Nat.succ_pos d)
  | Int.negSucc n =>
      match den with
      | 0 => ratZero
      | Nat.succ d => ratNeg (q (Nat.succ n) (Nat.succ d) (Nat.succ_pos d))

def qNat (n : Nat) : Rat :=
  ratNat n

def qNonneg (num : Nat) (den : Nat) (hden : 0 < den) : ratLe ratZero (q num den hden) :=
  RatNumKernel.ratDivApart_nonneg_of_nonneg_pos
    (RatNumKernel.ratNat_nonneg num)
    (RatNumLogEnclosure.ratNat_pos_of_pos hden)
    (RatNumLogEnclosure.ratNat_apart0_of_pos hden)

def PHASE_LN_BITS : Nat := 192
def PHASE_PI_BITS : Nat := 224
def SQRT_BITS : Nat := 192
def TRIG_K : Nat := 48
def OUT_BITS : Nat := 128

def tQ : Rat :=
  q 141347 10000 (by decide)

def qHalf : Rat :=
  q 1 2 (by decide)

theorem tQ_nonneg :
    ratLe ratZero tQ :=
  qNonneg 141347 10000 (by decide)

theorem qHalf_nonneg :
    ratLe ratZero qHalf :=
  qNonneg 1 2 (by decide)

structure QI where
  lo : Rat
  hi : Rat

namespace QI

def ordered (I : QI) : Prop :=
  ratLe I.lo I.hi

def width (I : QI) : Rat :=
  ratSub I.hi I.lo

def neg (I : QI) : QI :=
  { lo := ratNeg I.hi, hi := ratNeg I.lo }

def add (A B : QI) : QI :=
  { lo := ratAdd A.lo B.lo, hi := ratAdd A.hi B.hi }

def sub (A B : QI) : QI :=
  add A (neg B)

def scale (a : Rat) (I : QI) : QI :=
  { lo := ratMul a I.lo, hi := ratMul a I.hi }

def invPos (I : QI) (hlo : ratApart0 I.lo) (hhi : ratApart0 I.hi) : QI :=
  { lo := ratInvApart I.hi hhi, hi := ratInvApart I.lo hlo }

def ratMin (x y : Rat) : Rat :=
  if ratLeBool x y then x else y

def ratMax (x y : Rat) : Rat :=
  if ratLeBool x y then y else x

theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y :=
  RatNumLogEnclosure.ratLeBool_true_to_ratLe

theorem ratLe_to_ratLeBool {x y : Rat} :
    ratLe x y -> ratLeBool x y = true := by
  intro h
  unfold ratLeBool
  unfold ratLe BEDC.Derived.RationalUp.intLe at h
  exact BEDC.Derived.IntUp.natLeBool_true_of_le
    ((BEDC.Derived.IntUp.pairLe_iff_length_order
      (BEDC.Derived.RationalUp.intToPair_carrier _)
      (BEDC.Derived.RationalUp.intToPair_carrier _)).mp h)

theorem ratMin_le_left (x y : Rat) :
    ratLe (ratMin x y) x := by
  unfold ratMin
  cases h : ratLeBool x y with
  | true =>
      exact ratLe_refl x
  | false =>
      cases ratLe_total x y with
      | inl xy =>
          rw [ratLe_to_ratLeBool xy] at h
          cases h
      | inr yx =>
          exact yx

theorem ratMin_le_right (x y : Rat) :
    ratLe (ratMin x y) y := by
  unfold ratMin
  cases h : ratLeBool x y with
  | true =>
      exact ratLeBool_true_to_ratLe h
  | false =>
      exact ratLe_refl y

theorem ratMax_ge_left (x y : Rat) :
    ratLe x (ratMax x y) := by
  unfold ratMax
  cases h : ratLeBool x y with
  | true =>
      exact ratLeBool_true_to_ratLe h
  | false =>
      exact ratLe_refl x

theorem ratMax_ge_right (x y : Rat) :
    ratLe y (ratMax x y) := by
  unfold ratMax
  cases h : ratLeBool x y with
  | true =>
      exact ratLe_refl y
  | false =>
      cases ratLe_total x y with
      | inl xy =>
          rw [ratLe_to_ratLeBool xy] at h
          cases h
      | inr yx =>
          exact yx

theorem ratLe_neg_anti {a b : Rat} :
    ratLe a b -> ratLe (ratNeg b) (ratNeg a) := by
  intro h
  let t := ratAdd (ratNeg a) (ratNeg b)
  have shifted : ratLe (ratAdd a t) (ratAdd b t) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := a) (x' := b) (y := t) h
  have leftEq : RatEq (ratAdd a t) (ratNeg b) := by
    unfold t
    exact RatEq_trans _ _ _
      (RatEq_symm
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects
          (BEDC.Derived.LocatedReal.ratAdd_neg_local a)
          (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl b) (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (BEDC.Derived.LocatedReal.ratAdd_neg_local b)
            (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

theorem neg_ordered {I : QI} :
    QI.ordered I -> QI.ordered (neg I) := by
  intro h
  exact ratLe_neg_anti h

theorem add_ordered {A B : QI} :
    QI.ordered A -> QI.ordered B -> QI.ordered (add A B) := by
  intro hA hB
  exact RatNumKernel.ratAdd_le_add hA hB

theorem sub_ordered {A B : QI} :
    QI.ordered A -> QI.ordered B -> QI.ordered (sub A B) := by
  intro hA hB
  exact add_ordered hA (neg_ordered hB)

theorem scale_nonneg_ordered {a : Rat} {I : QI} :
    ratLe ratZero a -> QI.ordered I -> QI.ordered (scale a I) := by
  intro ha hI
  exact RatNumKernel.ratMul_le_mul_nonneg_left hI ha

def min4 (a b c d : Rat) : Rat :=
  ratMin (ratMin a b) (ratMin c d)

def max4 (a b c d : Rat) : Rat :=
  ratMax (ratMax a b) (ratMax c d)

theorem min4_le_first (a b c d : Rat) :
    ratLe (min4 a b c d) a := by
  unfold min4
  exact ratLe_trans
    (ratMin_le_left (ratMin a b) (ratMin c d))
    (ratMin_le_left a b)

theorem first_le_max4 (a b c d : Rat) :
    ratLe a (max4 a b c d) := by
  unfold max4
  exact ratLe_trans
    (ratMax_ge_left a b)
    (ratMax_ge_left (ratMax a b) (ratMax c d))

theorem min4_le_max4 (a b c d : Rat) :
    ratLe (min4 a b c d) (max4 a b c d) :=
  ratLe_trans (min4_le_first a b c d) (first_le_max4 a b c d)

def mul (A B : QI) : QI :=
  let p00 := ratMul A.lo B.lo
  let p01 := ratMul A.lo B.hi
  let p10 := ratMul A.hi B.lo
  let p11 := ratMul A.hi B.hi
  { lo := min4 p00 p01 p10 p11
    hi := max4 p00 p01 p10 p11 }

theorem mul_ordered (A B : QI) :
    QI.ordered (mul A B) := by
  unfold QI.ordered mul
  exact min4_le_max4
    (ratMul A.lo B.lo)
    (ratMul A.lo B.hi)
    (ratMul A.hi B.lo)
    (ratMul A.hi B.hi)

structure MulOrderedWitness (A B : QI) where
  ordered : QI.ordered (mul A B)

theorem mul_ordered_of_witness {A B : QI}
    (w : MulOrderedWitness A B) :
    QI.ordered (mul A B) :=
  w.ordered

def roundOut (_bits : Nat) (I : QI) : QI :=
  I

theorem roundOut_eq (bits : Nat) (I : QI) :
    roundOut bits I = I := by
  rfl

theorem roundOut_ordered (bits : Nat) {I : QI} :
    QI.ordered I -> QI.ordered (roundOut bits I) := by
  intro h
  exact h

end QI

def piI : QI :=
  { lo := RatNumTrig.piLo, hi := RatNumTrig.piHi }

def lnNI (n : Nat) : QI :=
  if h : 1 ≤ n then
    { lo := RatNumLogEnclosure.lnLo n (RatNumLogEnclosure.lnM96 n)
      hi := RatNumLogEnclosure.lnHi n (RatNumLogEnclosure.lnM96 n) h }
  else
    { lo := ratZero, hi := ratZero }

def thetaI (n : Nat) : QI :=
  QI.scale tQ (lnNI n)

def phaseK96 (n : Nat) : Nat :=
  if n = 1 then 0
  else if n ≤ 3 then 2
  else if n ≤ 4 then 3
  else if n ≤ 7 then 4
  else if n ≤ 11 then 5
  else if n ≤ 17 then 6
  else if n ≤ 28 then 7
  else if n ≤ 43 then 8
  else if n ≤ 68 then 9
  else 10

def twoPiKBox (k : Nat) : QI :=
  QI.scale (ratNat (2 * k)) piI

theorem twoPiKBox_ordered (k : Nat) :
    QI.ordered (twoPiKBox k) := by
  unfold twoPiKBox piI
  have hpi := RatNumTrig.piFormal_machin_M10_enclosed 0 0
  exact QI.scale_nonneg_ordered
    (RatNumKernel.ratNat_nonneg (2 * k))
    (ratLe_trans hpi.left hpi.right)

def redThetaI (n : Nat) : QI :=
  QI.sub (thetaI n) (twoPiKBox (phaseK96 n))

theorem redThetaI_unfold (n : Nat) :
    redThetaI n =
      { lo := ratAdd (ratMul tQ (lnNI n).lo)
          (ratNeg (ratMul (ratNat (2 * phaseK96 n)) RatNumTrig.piHi))
        hi := ratAdd (ratMul tQ (lnNI n).hi)
          (ratNeg (ratMul (ratNat (2 * phaseK96 n)) RatNumTrig.piLo)) } := by
  rfl

structure RangeReductionCert where
  n : Nat
  n_ge_one : 1 ≤ n
  n_le_96 : n ≤ 96
  k_le_10 : phaseK96 n ≤ 10
  reduced_ordered : QI.ordered (redThetaI n)
  reduced_ge_neg_piLo : ratLe (ratNeg RatNumTrig.piLo) (redThetaI n).lo
  reduced_le_piLo : ratLe (redThetaI n).hi RatNumTrig.piLo

def rangeReducedPhase (c : RangeReductionCert) : QI :=
  redThetaI c.n

structure RedThetaISmallRatNumObligation where
  all_small :
    ∀ n : Nat, 1 ≤ n -> n ≤ 96 ->
      QI.ordered (redThetaI n) ∧
      ratLe (ratNeg RatNumTrig.piLo) (redThetaI n).lo ∧
      ratLe (redThetaI n).hi RatNumTrig.piLo

theorem redThetaI_small_1_96_from_obligation
    (cert : RedThetaISmallRatNumObligation)
    {n : Nat}
    (hn1 : 1 ≤ n)
    (hn96 : n ≤ 96) :
    QI.ordered (redThetaI n) ∧
      ratLe (ratNeg RatNumTrig.piLo) (redThetaI n).lo ∧
      ratLe (redThetaI n).hi RatNumTrig.piLo :=
  cert.all_small n hn1 hn96

def zForLn (n : Nat) : Rat :=
  RatNumLogEnclosure.zOfNat n

def lnSeriesCert (n : Nat) (hn : 1 ≤ n) :
    RatNumLogEnclosure.SeriesEnclosedFrom
      (fun K => RatNumLogEnclosure.atanhFormalSeries (zForLn n) K)
      (RatNumLogEnclosure.lnM96 n)
      (lnNI n).lo
      (lnNI n).hi := by
  unfold lnNI zForLn
  simp [hn]
  exact RatNumLogEnclosure.formal_lnN_enclosure n
    (RatNumLogEnclosure.lnM96 n) hn

structure SqrtNatBoxCert where
  n : Nat
  I : QI
  lo_apart : ratApart0 I.lo
  hi_apart : ratApart0 I.hi
  sqrt_ordered : QI.ordered I
  sq_lo_le_n : ratLe (ratMul I.lo I.lo) (ratNat n)
  n_le_sq_hi : ratLe (ratNat n) (ratMul I.hi I.hi)

def rhoI (s : SqrtNatBoxCert) : QI :=
  QI.invPos s.I s.lo_apart s.hi_apart

def SqrtNatBoxContainsSq (n : Nat) (I : QI) : Prop :=
  QI.ordered I ∧
    ratLe (ratMul I.lo I.lo) (ratNat n) ∧
    ratLe (ratNat n) (ratMul I.hi I.hi)

theorem sqrtNatBoxCert_contains_sq (s : SqrtNatBoxCert) :
    SqrtNatBoxContainsSq s.n s.I := by
  exact And.intro s.sqrt_ordered (And.intro s.sq_lo_le_n s.n_le_sq_hi)

structure RhoNatBoxCert where
  sqrt : SqrtNatBoxCert

def sqrtNatBoxWide96 (n : Nat) (hn1 : 1 ≤ n) (hn96 : n ≤ 96) :
    SqrtNatBoxCert :=
  { n := n
    I := { lo := ratNat 1, hi := ratNat 96 }
    lo_apart := RatNumLogEnclosure.ratNat_apart0_of_pos (by decide)
    hi_apart := RatNumLogEnclosure.ratNat_apart0_of_pos (by decide)
    sqrt_ordered := RatNumKernel.ratNat_le_of_nat_le (by decide)
    sq_lo_le_n := by
      exact RatNumKernel.ratLe_of_RatEq_left
        (RatNumLogEnclosure.ratNat_mul 1 1)
        (RatNumKernel.ratNat_le_of_nat_le hn1)
    n_le_sq_hi := by
      have hwide : n ≤ 96 * 96 := Nat.le_trans hn96 (by decide)
      exact RatNumKernel.ratLe_of_RatEq_right
        (RatNumKernel.ratNat_le_of_nat_le hwide)
        (RatEq_symm (RatNumLogEnclosure.ratNat_mul 96 96)) }

theorem sqrtNatBoxWide96_contains_sq
    (n : Nat) (hn1 : 1 ≤ n) (hn96 : n ≤ 96) :
    SqrtNatBoxContainsSq n (sqrtNatBoxWide96 n hn1 hn96).I := by
  exact sqrtNatBoxCert_contains_sq (sqrtNatBoxWide96 n hn1 hn96)

theorem sqrtNatBoxWide96_ordered
    (n : Nat) (hn1 : 1 ≤ n) (hn96 : n ≤ 96) :
    QI.ordered (sqrtNatBoxWide96 n hn1 hn96).I :=
  (sqrtNatBoxWide96_contains_sq n hn1 hn96).left

theorem sqrtNatBoxWide96_sq_lo_le_n
    (n : Nat) (hn1 : 1 ≤ n) (hn96 : n ≤ 96) :
    ratLe
      (ratMul (sqrtNatBoxWide96 n hn1 hn96).I.lo
        (sqrtNatBoxWide96 n hn1 hn96).I.lo)
      (ratNat n) :=
  (sqrtNatBoxWide96_contains_sq n hn1 hn96).right.left

theorem sqrtNatBoxWide96_n_le_sq_hi
    (n : Nat) (hn1 : 1 ≤ n) (hn96 : n ≤ 96) :
    ratLe
      (ratNat n)
      (ratMul (sqrtNatBoxWide96 n hn1 hn96).I.hi
        (sqrtNatBoxWide96 n hn1 hn96).I.hi) :=
  (sqrtNatBoxWide96_contains_sq n hn1 hn96).right.right

inductive TrigBoxBridgeObligation : Type
  | reducedPhaseTrigEnclosure

structure TrigBoxCert where
  range : RangeReductionCert
  sin : QI
  cos : QI
  sin_ordered : QI.ordered sin
  cos_ordered : QI.ordered cos
  bridge : TrigBoxBridgeObligation

structure CBox where
  re : QI
  im : QI

namespace CBox

def roundOut (bits : Nat) (B : CBox) : CBox :=
  { re := QI.roundOut bits B.re
    im := QI.roundOut bits B.im }

theorem roundOut_eq (bits : Nat) (B : CBox) :
    roundOut bits B = B := by
  rfl

theorem roundOut_ordered (bits : Nat) {B : CBox} :
    QI.ordered B.re -> QI.ordered B.im ->
      QI.ordered (roundOut bits B).re ∧ QI.ordered (roundOut bits B).im := by
  intro hre him
  exact And.intro hre him

end CBox

structure CBoxMulOrderedWitness (rho : RhoNatBoxCert) (trig : TrigBoxCert) where
  re : QI.MulOrderedWitness (rhoI rho.sqrt) trig.cos
  im : QI.MulOrderedWitness (rhoI rho.sqrt) trig.sin

def powNegCBoxRaw (rho : RhoNatBoxCert) (trig : TrigBoxCert) : CBox :=
  let R := rhoI rho.sqrt
  let C := trig.cos
  let S := trig.sin
  { re := QI.mul R C
    im := QI.neg (QI.mul R S) }

theorem powNegCBoxRaw_re_ordered_of_witness
    {rho : RhoNatBoxCert} {trig : TrigBoxCert}
    (w : CBoxMulOrderedWitness rho trig) :
    QI.ordered (powNegCBoxRaw rho trig).re := by
  exact QI.mul_ordered_of_witness w.re

theorem powNegCBoxRaw_re_ordered
    (rho : RhoNatBoxCert) (trig : TrigBoxCert) :
    QI.ordered (powNegCBoxRaw rho trig).re := by
  exact QI.mul_ordered (rhoI rho.sqrt) trig.cos

theorem powNegCBoxRaw_im_ordered_of_witness
    {rho : RhoNatBoxCert} {trig : TrigBoxCert}
    (w : CBoxMulOrderedWitness rho trig) :
    QI.ordered (powNegCBoxRaw rho trig).im := by
  exact QI.neg_ordered (QI.mul_ordered_of_witness w.im)

theorem powNegCBoxRaw_im_ordered
    (rho : RhoNatBoxCert) (trig : TrigBoxCert) :
    QI.ordered (powNegCBoxRaw rho trig).im := by
  exact QI.neg_ordered (QI.mul_ordered (rhoI rho.sqrt) trig.sin)

theorem powNegCBoxRaw_ordered_of_witness
    {rho : RhoNatBoxCert} {trig : TrigBoxCert}
    (w : CBoxMulOrderedWitness rho trig) :
    QI.ordered (powNegCBoxRaw rho trig).re ∧
      QI.ordered (powNegCBoxRaw rho trig).im := by
  exact And.intro
    (powNegCBoxRaw_re_ordered_of_witness w)
    (powNegCBoxRaw_im_ordered_of_witness w)

theorem powNegCBoxRaw_ordered
    (rho : RhoNatBoxCert) (trig : TrigBoxCert) :
    QI.ordered (powNegCBoxRaw rho trig).re ∧
      QI.ordered (powNegCBoxRaw rho trig).im := by
  exact And.intro
    (powNegCBoxRaw_re_ordered rho trig)
    (powNegCBoxRaw_im_ordered rho trig)

def powNegCBox (rho : RhoNatBoxCert) (trig : TrigBoxCert) : CBox :=
  CBox.roundOut OUT_BITS (powNegCBoxRaw rho trig)

theorem powNegCBox_ordered_of_witness
    {rho : RhoNatBoxCert} {trig : TrigBoxCert}
    (w : CBoxMulOrderedWitness rho trig) :
    QI.ordered (powNegCBox rho trig).re ∧
      QI.ordered (powNegCBox rho trig).im := by
  exact CBox.roundOut_ordered OUT_BITS
    (powNegCBoxRaw_re_ordered_of_witness w)
    (powNegCBoxRaw_im_ordered_of_witness w)

theorem powNegCBox_ordered
    (rho : RhoNatBoxCert) (trig : TrigBoxCert) :
    QI.ordered (powNegCBox rho trig).re ∧
      QI.ordered (powNegCBox rho trig).im := by
  exact CBox.roundOut_ordered OUT_BITS
    (powNegCBoxRaw_re_ordered rho trig)
    (powNegCBoxRaw_im_ordered rho trig)

structure PowNegCPhaseBoxCert where
  n : Nat
  range : RangeReductionCert
  rho : RhoNatBoxCert
  trig : TrigBoxCert
  same_n_range : range.n = n
  same_n_rho : rho.sqrt.n = n
  trig_matches_range : trig.range = range
  re_ordered : QI.ordered (powNegCBox rho trig).re
  im_ordered : QI.ordered (powNegCBox rho trig).im

def zetaPowInput96 (c : PowNegCPhaseBoxCert) : CBox :=
  powNegCBox c.rho c.trig

inductive PhaseBoxBridgeObligation : Type
  | lnNatAnalyticBridge
  | sqrtNatAnalyticBridge
  | sinCosAnalyticBridge
  | trigonometricPeriodBridge
  | eulerHalfLineBridge
  deriving DecidableEq

structure HonestPowNegCBridgeObligation where
  n : Nat
  n_ge_one : 1 ≤ n
  phase_box : PowNegCPhaseBoxCert
  obligations : List PhaseBoxBridgeObligation

def powNegCBridgeObligations (c : PowNegCPhaseBoxCert)
    (hn : 1 ≤ c.n) : HonestPowNegCBridgeObligation :=
  { n := c.n
    n_ge_one := hn
    phase_box := c
    obligations :=
      [ PhaseBoxBridgeObligation.lnNatAnalyticBridge,
        PhaseBoxBridgeObligation.sqrtNatAnalyticBridge,
        PhaseBoxBridgeObligation.sinCosAnalyticBridge,
        PhaseBoxBridgeObligation.trigonometricPeriodBridge,
        PhaseBoxBridgeObligation.eulerHalfLineBridge ] }

theorem powNegCBridgeObligations_readback
    (c : PowNegCPhaseBoxCert)
    (hn : 1 ≤ c.n) :
    (powNegCBridgeObligations c hn).obligations =
      [ PhaseBoxBridgeObligation.lnNatAnalyticBridge,
        PhaseBoxBridgeObligation.sqrtNatAnalyticBridge,
        PhaseBoxBridgeObligation.sinCosAnalyticBridge,
        PhaseBoxBridgeObligation.trigonometricPeriodBridge,
        PhaseBoxBridgeObligation.eulerHalfLineBridge ] := by
  rfl

theorem powNegCBox_analytic_bridge_obligation
    (c : PowNegCPhaseBoxCert)
    (hn : 1 ≤ c.n) :
    PhaseBoxBridgeObligation.trigonometricPeriodBridge ∈
      (powNegCBridgeObligations c hn).obligations := by
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

end BEDC.Real.RatNumPhaseBox
