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

def PHASE_LN_BITS : Nat := 192
def PHASE_PI_BITS : Nat := 224
def SQRT_BITS : Nat := 192
def TRIG_K : Nat := 48
def OUT_BITS : Nat := 128

def tQ : Rat :=
  q 141347 10000 (by decide)

def qHalf : Rat :=
  q 1 2 (by decide)

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

def min4 (a b c d : Rat) : Rat :=
  ratMin (ratMin a b) (ratMin c d)

def max4 (a b c d : Rat) : Rat :=
  ratMax (ratMax a b) (ratMax c d)

def mul (A B : QI) : QI :=
  let p00 := ratMul A.lo B.lo
  let p01 := ratMul A.lo B.hi
  let p10 := ratMul A.hi B.lo
  let p11 := ratMul A.hi B.hi
  { lo := min4 p00 p01 p10 p11
    hi := max4 p00 p01 p10 p11 }

def roundOut (_bits : Nat) (I : QI) : QI :=
  I

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

end CBox

def powNegCBoxRaw (rho : RhoNatBoxCert) (trig : TrigBoxCert) : CBox :=
  let R := rhoI rho.sqrt
  let C := trig.cos
  let S := trig.sin
  { re := QI.mul R C
    im := QI.neg (QI.mul R S) }

def powNegCBox (rho : RhoNatBoxCert) (trig : TrigBoxCert) : CBox :=
  CBox.roundOut OUT_BITS (powNegCBoxRaw rho trig)

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

end BEDC.Real.RatNumPhaseBox
