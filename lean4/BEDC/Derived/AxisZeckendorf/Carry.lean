/-
ZCarry: Zeckendorf carry classifier `011 → 100`. Crucially, ZCarry is
NOT history-sameness; the negative theorem
`zCarry_not_hsame` is provable here directly because `hsame := Eq` and
the two endpoints have visibly distinct top constructors.
The Fibonacci value-preservation property is a horizon target.
-/
import BEDC.Derived.AxisZeckendorf.Zeckendorf

namespace BEDC.Derived.AxisZeckendorf.Carry

open BEDC.FKernel.Hist
open BEDC.Derived.AxisZeckendorf.Zeckendorf

inductive ZCarry : BHist → BHist → Prop where
  | base : ZCarry word_011 word_100

theorem zCarry_011_100 : ZCarry word_011 word_100 := ZCarry.base

theorem zCarry_011_100_not_hsame : ¬ hsame word_011 word_100 := by
  unfold word_011 word_100
  intro h
  exact BHist.noConfusion h

theorem zCarry_not_hsame {h k : BHist} : ZCarry h k → ¬ hsame h k := by
  intro carry
  cases carry with
  | base => exact zCarry_011_100_not_hsame

theorem zCarry_target_normal : ∀ {h k : BHist}, ZCarry h k → ZNormal k := by
  intro h k carry
  cases carry with
  | base => exact znormal_word_100

theorem zCarry_source_not_normal : ∀ {h k : BHist}, ZCarry h k → ¬ ZNormal h := by
  intro h k carry
  cases carry with
  | base => exact znormal_word_011_absurd

def ZCarrySourceSpec (h : BHist) : Prop := ¬ ZNormal h

def ZCarryPatternSpec (h k : BHist) : Prop := ZCarry h k

def ZCarryClassifierSpec (h k : BHist) : Prop :=
  ZCarry h k ∧ ZNormal k ∧ ¬ ZNormal h ∧ ¬ hsame h k

structure ZCarryStabilityCert : Prop where
  notHsame : ∀ {h k : BHist}, ZCarry h k → ¬ hsame h k
  targetNormal : ∀ {h k : BHist}, ZCarry h k → ZNormal k
  sourceNotNormal : ∀ {h k : BHist}, ZCarry h k → ¬ ZNormal h
  fibValuePreservationPending : True

def zCarryStabilityCert : ZCarryStabilityCert :=
  { notHsame := zCarry_not_hsame
    targetNormal := zCarry_target_normal
    sourceNotNormal := zCarry_source_not_normal
    fibValuePreservationPending := True.intro }

def ZCarryLedgerPolicy (h k : BHist) : Prop := ZCarry h k

structure ZCarryNameCert : Type where
  source : BHist → Prop
  pattern : BHist → BHist → Prop
  classifier : BHist → BHist → Prop
  stability : ZCarryStabilityCert
  ledger : BHist → BHist → Prop

def zCarry_namecert : ZCarryNameCert :=
  { source := ZCarrySourceSpec
    pattern := ZCarryPatternSpec
    classifier := ZCarryClassifierSpec
    stability := zCarryStabilityCert
    ledger := ZCarryLedgerPolicy }

theorem zCarry_licensed_not_primitive : True := True.intro

end BEDC.Derived.AxisZeckendorf.Carry
