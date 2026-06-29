import BEDC.Real.RatLogEnclosure
import BEDC.Derived.LocatedTranscendental

set_option maxHeartbeats 1000000

namespace BEDC.Real.LocatedNatPowerEnclosure

open BEDC.Derived.LocatedReal
open BEDC.Derived.LocatedTranscendental
open BEDC.Derived.RationalUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)

abbrev IRat : Type :=
  BEDC.Real.RatInterval.Rat

abbrev LRat : Type :=
  BEDC.Derived.RationalUp.RatNum

structure LogAtanhWindow where
  n : Nat
  M : Nat
  K : Nat

namespace LogAtanhWindow

def cert (w : LogAtanhWindow) :
    BEDC.Real.RatLogEnclosure.LogNatArithCert :=
  { n := w.n, M := w.M, K := w.K }

def lo (w : LogAtanhWindow) : IRat :=
  BEDC.Real.RatLogEnclosure.logLoSmall w.n w.M

def hi (w : LogAtanhWindow) : IRat :=
  BEDC.Real.RatLogEnclosure.logHiSmall w.n w.M

def check (w : LogAtanhWindow) : Bool :=
  BEDC.Real.RatLogEnclosure.LogNatArithCert.check (cert w)

def Sound (w : LogAtanhWindow) : Prop :=
  BEDC.Real.RatLogEnclosure.LogNatArithCert.Sound (cert w)

theorem sound (w : LogAtanhWindow) :
    check w = true -> Sound w := by
  intro h
  exact BEDC.Real.RatLogEnclosure.logNat_arith_sound (cert w) h

theorem ordered {w : LogAtanhWindow} :
    Sound w -> w.lo <= w.hi := by
  intro h
  exact h.right.right.right.right

end LogAtanhWindow

private theorem natLeBool_true_to_le {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

theorem ratLeBool_true_to_ratLe {x y : LRat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

theorem ratLtBool_true_to_ratLt {x y : LRat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

structure ExpWindowOrderCert where
  x : LRat
  xBound : Nat
  precision : Nat

namespace ExpWindowOrderCert

def window (c : ExpWindowOrderCert) : RatWindow :=
  expWindow c.x c.xBound c.precision

def lo (c : ExpWindowOrderCert) : LRat :=
  (window c).lo

def hi (c : ExpWindowOrderCert) : LRat :=
  (window c).hi

def check (c : ExpWindowOrderCert) : Bool :=
  ratLeBool c.lo c.hi

def Sound (c : ExpWindowOrderCert) : Prop :=
  ratLe c.lo c.hi

theorem sound (c : ExpWindowOrderCert) :
    check c = true -> Sound c := by
  intro h
  exact ratLeBool_true_to_ratLe h

end ExpWindowOrderCert

structure NatSigmaPowerWindow where
  sigma : LRat
  logWindow : LogAtanhWindow
  expCert : ExpWindowOrderCert

namespace NatSigmaPowerWindow

def n (w : NatSigmaPowerWindow) : Nat :=
  w.logWindow.n

def logLo (w : NatSigmaPowerWindow) : IRat :=
  w.logWindow.lo

def logHi (w : NatSigmaPowerWindow) : IRat :=
  w.logWindow.hi

def lo (w : NatSigmaPowerWindow) : LRat :=
  w.expCert.lo

def hi (w : NatSigmaPowerWindow) : LRat :=
  w.expCert.hi

def check (w : NatSigmaPowerWindow) : Bool :=
  BEDC.Derived.IntUp.natLeBool 2 w.n &&
    (LogAtanhWindow.check w.logWindow &&
      (ratLtBool ratZero w.sigma &&
        (ratLtBool w.sigma ratOne && ExpWindowOrderCert.check w.expCert)))

structure Sound (w : NatSigmaPowerWindow) : Prop where
  n_ge_two : 2 ≤ w.n
  log_sound : LogAtanhWindow.Sound w.logWindow
  sigma_pos : ratLt ratZero w.sigma
  sigma_lt_one : ratLt w.sigma ratOne
  exp_ordered : ExpWindowOrderCert.Sound w.expCert

theorem sound (w : NatSigmaPowerWindow) :
    check w = true -> Sound w := by
  intro h
  unfold check at h
  have hnBool :
      BEDC.Derived.IntUp.natLeBool 2 w.n = true :=
    BEDC.Real.RatInterval.boolAndLeftTrue h
  have htail :
      (LogAtanhWindow.check w.logWindow &&
        (ratLtBool ratZero w.sigma &&
          (ratLtBool w.sigma ratOne && ExpWindowOrderCert.check w.expCert))) = true :=
    BEDC.Real.RatInterval.boolAndRightTrue h
  have hlogBool : LogAtanhWindow.check w.logWindow = true :=
    BEDC.Real.RatInterval.boolAndLeftTrue htail
  have hafterLog :
      (ratLtBool ratZero w.sigma &&
        (ratLtBool w.sigma ratOne && ExpWindowOrderCert.check w.expCert)) = true :=
    BEDC.Real.RatInterval.boolAndRightTrue htail
  have hsigmaPosBool : ratLtBool ratZero w.sigma = true :=
    BEDC.Real.RatInterval.boolAndLeftTrue hafterLog
  have hafterSigma :
      (ratLtBool w.sigma ratOne && ExpWindowOrderCert.check w.expCert) = true :=
    BEDC.Real.RatInterval.boolAndRightTrue hafterLog
  have hsigmaLtOneBool : ratLtBool w.sigma ratOne = true :=
    BEDC.Real.RatInterval.boolAndLeftTrue hafterSigma
  have hexpBool : ExpWindowOrderCert.check w.expCert = true :=
    BEDC.Real.RatInterval.boolAndRightTrue hafterSigma
  exact
    { n_ge_two := natLeBool_true_to_le hnBool
      log_sound := LogAtanhWindow.sound w.logWindow hlogBool
      sigma_pos := ratLtBool_true_to_ratLt hsigmaPosBool
      sigma_lt_one := ratLtBool_true_to_ratLt hsigmaLtOneBool
      exp_ordered := ExpWindowOrderCert.sound w.expCert hexpBool }

theorem log_ordered {w : NatSigmaPowerWindow} :
    Sound w -> w.logLo <= w.logHi := by
  intro h
  exact LogAtanhWindow.ordered h.log_sound

theorem exp_ordered {w : NatSigmaPowerWindow} :
    Sound w -> ratLe w.lo w.hi := by
  intro h
  exact h.exp_ordered

end NatSigmaPowerWindow

def locatedNatPowerAtom
    (x : LRat) (xBound : Nat) (evidence : ExpLocatedEvidence x xBound) :
    LocatedReal :=
  expLocated x xBound evidence

def ratOfInt (z : Int) : LRat :=
  match z with
  | Int.ofNat n => natRat n
  | Int.negSucc n => ratNeg (natRat (Nat.succ n))

private theorem natToUnary_pos_den {n : Nat} :
    0 < n ->
      BEDC.Derived.NatUp.NatUnaryStrictPrefix BEDC.Derived.PadicUp.NatOne
          (BEDC.Derived.IntUp.natToUnary n) ∨
        hsame (BEDC.Derived.IntUp.natToUnary n) BEDC.Derived.PadicUp.NatOne := by
  intro h
  cases n with
  | zero =>
      cases h
  | succ n =>
      cases n with
      | zero =>
          exact Or.inr rfl
      | succ n =>
          apply Or.inl
          apply BEDC.Derived.PadicUp.NatUnaryStrictPrefix_of_length_lt
          · exact unary_e1_closed unary_empty
          · exact BEDC.Derived.IntUp.natToUnary_unary (Nat.succ (Nat.succ n))
          · rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
              BHist.Empty unary_empty]
            rw [BEDC.Derived.IntUp.natToUnary_length]
            exact Nat.succ_lt_succ (Nat.zero_lt_succ n)

theorem natRat_positive {n : Nat} :
    0 < n -> RatPositive (natRat n) := by
  intro h
  constructor
  · rfl
  · unfold ratApart0 BEDC.Derived.RationalUp.intApart0 natRat
      BEDC.Derived.RationalUp.intToRat BEDC.Derived.RationalUp.intOfNat
      natHist
    exact natToUnary_pos_den h

def ratOfIntervalRat (q : IRat) : LRat :=
  let numerator := ratOfInt q.num
  let denominator :=
    { num := BEDC.Derived.RationalUp.intOne
      den := BEDC.Derived.IntUp.natToUnary q.den
      den_pos := by
        exact natToUnary_pos_den q.den_pos }
  ratMul numerator denominator

def locatedInterval (lo hi : LRat) (x : LocatedReal) : Prop :=
  locatedLower lo x ∧ locatedUpper x hi

def locatedLnNatObligation (w : NatSigmaPowerWindow) (lnNat : LocatedReal) :
    Prop :=
  locatedInterval (ratOfIntervalRat w.logLo) (ratOfIntervalRat w.logHi) lnNat

def exponentFromSigmaLog (sigma : LRat) (lnApprox : LRat) : LRat :=
  ratNeg (ratMul sigma lnApprox)

def expInputIntervalObligation (w : NatSigmaPowerWindow)
    (expInput : LocatedReal) : Prop :=
  locatedInterval (exponentFromSigmaLog w.sigma (ratOfIntervalRat w.logHi))
    (exponentFromSigmaLog w.sigma (ratOfIntervalRat w.logLo)) expInput

structure LocatedNatPowerBridge
    (w : NatSigmaPowerWindow)
    (evidence : ExpLocatedEvidence w.expCert.x w.expCert.xBound) where
  ln_positive : RatPositive (natRat w.n)
  ln_evidence : LnLocatedEvidence (natRat w.n) ln_positive
  expInput : LocatedReal
  atanh_log_window_matches_located_ln_nat :
    locatedLnNatObligation w
      (lnLocated (natRat w.n) ln_positive ln_evidence)
  exp_input_matches_neg_sigma_log :
    expInputIntervalObligation w expInput
  exp_input_matches_window_source :
    locatedEq expInput (ratLocated w.expCert.x)

structure LocatedNatPowerEnclosure
    (w : NatSigmaPowerWindow)
    (evidence : ExpLocatedEvidence w.expCert.x w.expCert.xBound) where
  arithmetic_sound : NatSigmaPowerWindow.Sound w
  bridge : LocatedNatPowerBridge w evidence
  lower :
    locatedLower w.lo
      (locatedNatPowerAtom w.expCert.x w.expCert.xBound evidence)
  upper :
    locatedUpper
      (locatedNatPowerAtom w.expCert.x w.expCert.xBound evidence) w.hi

def natPowLocated_enclosure_with_bridge
    (w : NatSigmaPowerWindow)
    (evidence : ExpLocatedEvidence w.expCert.x w.expCert.xBound)
    (hcheck : NatSigmaPowerWindow.check w = true)
    (bridge : LocatedNatPowerBridge w evidence) :
    LocatedNatPowerEnclosure w evidence := by
  exact
    { arithmetic_sound := NatSigmaPowerWindow.sound w hcheck
      bridge := bridge
      lower := exp_located_lower w.expCert.x w.expCert.xBound evidence
        w.expCert.precision
      upper := exp_located_upper w.expCert.x w.expCert.xBound evidence
        w.expCert.precision }

theorem natPowLocated_enclosed_with_bridge
    (w : NatSigmaPowerWindow)
    (evidence : ExpLocatedEvidence w.expCert.x w.expCert.xBound)
    (hcheck : NatSigmaPowerWindow.check w = true)
    (bridge : LocatedNatPowerBridge w evidence) :
    locatedLower w.lo
      (locatedNatPowerAtom w.expCert.x w.expCert.xBound evidence) ∧
      locatedUpper
        (locatedNatPowerAtom w.expCert.x w.expCert.xBound evidence) w.hi := by
  let cert := natPowLocated_enclosure_with_bridge w evidence hcheck bridge
  exact ⟨cert.lower, cert.upper⟩

theorem expLocated_window_enclosed
    (x : LRat) (xBound precision : Nat)
    (evidence : ExpLocatedEvidence x xBound) :
    locatedLower (expWindow x xBound precision).lo
      (expLocated x xBound evidence) ∧
      locatedUpper (expLocated x xBound evidence)
        (expWindow x xBound precision).hi := by
  exact ⟨exp_located_lower x xBound evidence precision,
    exp_located_upper x xBound evidence precision⟩

end BEDC.Real.LocatedNatPowerEnclosure
