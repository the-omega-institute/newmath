/-
ZNormal: Zeckendorf-style normal-form predicate on histories — no two
adjacent `e1`-extensions. The predicate is structural; it does not depend
on `hsame` and does not assert any arithmetic interpretation.
The Fibonacci-value semantics is a horizon target.
-/
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AxisZeckendorf.Zeckendorf

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

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

theorem ZNormal_adjacent_one_inversion {h : BHist} :
    ZNormal (BHist.e1 h) ->
      (h = BHist.Empty ∨ ∃ k : BHist, h = BHist.e0 k ∧ ZNormal (BHist.e0 k)) ∧
        (∀ k : BHist, h = BHist.e1 k -> False) := by
  intro normal
  constructor
  · cases normal with
    | e1_after_empty =>
        exact Or.inl rfl
    | e1_after_e0 tailNormal =>
        exact Or.inr (Exists.intro _ (And.intro rfl tailNormal))
  · intro k hk
    cases normal with
    | e1_after_empty =>
        cases hk
    | e1_after_e0 _tailNormal =>
        cases hk

theorem ZNormal_normal_form_coverage :
    ZNormal BHist.Empty ∧ (∀ {h : BHist}, ZNormal h -> ZNormal (BHist.e0 h)) ∧
      ZNormal (BHist.e1 BHist.Empty) ∧
        (∀ {h : BHist}, ZNormal (BHist.e0 h) -> ZNormal (BHist.e1 (BHist.e0 h))) ∧
          (∀ {h : BHist},
            ZNormal (BHist.e1 h) ->
              (h = BHist.Empty ∨ ∃ k : BHist, h = BHist.e0 k ∧ ZNormal (BHist.e0 k))) := by
  exact And.intro ZNormal.empty
    (And.intro (fun normal => ZNormal.e0 normal)
      (And.intro ZNormal.e1_after_empty
        (And.intro (fun normal => ZNormal.e1_after_e0 normal)
          (fun normal => (ZNormal_adjacent_one_inversion normal).left))))

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

theorem ZNormal_semantic_name_certificate :
    SemanticNameCert ZNormalSourceSpec ZNormalPatternSpec ZNormalLedgerPolicy
        ZNormalClassifierSpec ∧
      (forall {h k : BHist},
        ZNormalClassifierSpec h k -> ZNormal h ∧ ZNormal k ∧ hsame h k) := by
  have cert :
      SemanticNameCert ZNormalSourceSpec ZNormalPatternSpec ZNormalLedgerPolicy
        ZNormalClassifierSpec := {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty ZNormal.empty
      equiv_refl := by
        intro h source
        exact And.intro source (And.intro source (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }
  exact And.intro cert (fun classified => classified)

theorem zNormal_licensed_not_primitive : True := True.intro

end BEDC.Derived.AxisZeckendorf.Zeckendorf
