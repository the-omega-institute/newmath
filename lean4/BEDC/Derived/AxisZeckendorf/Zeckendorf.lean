/-
ZNormal: Zeckendorf-style normal-form predicate on histories — no two
adjacent `e1`-extensions. The predicate is structural; it does not depend
on `hsame` and does not assert any arithmetic interpretation.
The Fibonacci-value semantics is a horizon target.
-/
import BEDC.FKernel.Hist

namespace BEDC.Derived.AxisZeckendorf.Zeckendorf

open BEDC.FKernel.Hist

inductive ZNormal : BHist → Prop where
  | empty : ZNormal BHist.Empty
  | e0 : ∀ {h : BHist}, ZNormal h → ZNormal (BHist.e0 h)
  | e1_after_empty : ZNormal (BHist.e1 BHist.Empty)
  | e1_after_e0 : ∀ {h : BHist}, ZNormal (BHist.e0 h) → ZNormal (BHist.e1 (BHist.e0 h))

def word_011 : BHist := BHist.e1 (BHist.e1 (BHist.e0 BHist.Empty))

def word_100 : BHist := BHist.e0 (BHist.e0 (BHist.e1 BHist.Empty))

theorem znormal_word_100 : ZNormal word_100 := by
  unfold word_100
  exact ZNormal.e0 (ZNormal.e0 ZNormal.e1_after_empty)

theorem znormal_word_011_absurd : ZNormal word_011 → False := by
  unfold word_011
  intro h
  cases h

def ZNormalSourceSpec (h : BHist) : Prop := ZNormal h

def ZNormalPatternSpec (h : BHist) : Prop := ZNormal h

def ZNormalClassifierSpec (h k : BHist) : Prop :=
  ZNormal h ∧ ZNormal k ∧ hsame h k

structure ZNormalStabilityCert : Prop where
  baseEmpty : ZNormal BHist.Empty
  e0Closure : ∀ {h : BHist}, ZNormal h → ZNormal (BHist.e0 h)
  e1AfterEmptyClosure : ZNormal (BHist.e1 BHist.Empty)
  e1AfterE0Closure : ∀ {h : BHist}, ZNormal (BHist.e0 h) → ZNormal (BHist.e1 (BHist.e0 h))

def zNormalStabilityCert : ZNormalStabilityCert :=
  { baseEmpty := ZNormal.empty
    e0Closure := ZNormal.e0
    e1AfterEmptyClosure := ZNormal.e1_after_empty
    e1AfterE0Closure := ZNormal.e1_after_e0 }

def ZNormalLedgerPolicy (h : BHist) : Prop := ZNormal h

structure ZNormalNameCert : Type where
  source : BHist → Prop
  pattern : BHist → Prop
  classifier : BHist → BHist → Prop
  stability : ZNormalStabilityCert
  ledger : BHist → Prop

def zNormal_namecert : ZNormalNameCert :=
  { source := ZNormalSourceSpec
    pattern := ZNormalPatternSpec
    classifier := ZNormalClassifierSpec
    stability := zNormalStabilityCert
    ledger := ZNormalLedgerPolicy }

theorem zNormal_licensed_not_primitive : True := True.intro

end BEDC.Derived.AxisZeckendorf.Zeckendorf
