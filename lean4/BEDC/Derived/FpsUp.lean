import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def FpsSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def FpsSingletonClassifier (h k : BHist) : Prop :=
  FpsSingletonCarrier h ∧ FpsSingletonCarrier k ∧ hsame h k

def FpsSingletonZero : BHist :=
  BHist.Empty

def FpsSingletonOne : BHist :=
  BHist.Empty

def FpsSingletonCoeff (_F _n : BHist) : BHist :=
  BHist.Empty

def FpsSingletonAdd (_F _G : BHist) : BHist :=
  BHist.Empty

def FpsSingletonMul (_F _G : BHist) : BHist :=
  BHist.Empty

theorem fps_singleton_empty_schema_laws :
    SemanticNameCert FpsSingletonCarrier FpsSingletonCarrier FpsSingletonCarrier
      FpsSingletonClassifier ∧
      FpsSingletonCarrier FpsSingletonZero ∧
      FpsSingletonCarrier FpsSingletonOne ∧
      (forall F n : BHist, FpsSingletonCarrier (FpsSingletonCoeff F n)) ∧
      (forall {F G : BHist}, FpsSingletonCarrier F -> FpsSingletonCarrier G ->
        FpsSingletonCarrier (FpsSingletonAdd F G) ∧
          FpsSingletonCarrier (FpsSingletonMul F G)) ∧
      (forall {F G F' G' : BHist}, FpsSingletonClassifier F F' ->
        FpsSingletonClassifier G G' ->
          FpsSingletonClassifier (FpsSingletonAdd F G) (FpsSingletonAdd F' G') ∧
            FpsSingletonClassifier (FpsSingletonMul F G) (FpsSingletonMul F' G')) := by
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : FpsSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
        equiv_refl := by
          intro h carrier
          exact And.intro carrier (And.intro carrier (hsame_refl h))
        equiv_symm := by
          intro h k same
          exact And.intro same.right.left
            (And.intro same.left (hsame_symm same.right.right))
        equiv_trans := by
          intro h k r sameHK sameKR
          exact And.intro sameHK.left
            (And.intro sameKR.right.left
              (hsame_trans sameHK.right.right sameKR.right.right))
        carrier_respects_equiv := by
          intro h k same _carrier
          exact same.right.left
      }
      pattern_sound := by
        intro _h source
        exact source
      ledger_sound := by
        intro _h source
        exact source
    }
  · constructor
    · exact emptyCarrier
    · constructor
      · exact emptyCarrier
      · constructor
        · intro F n
          exact emptyCarrier
        · constructor
          · intro F G _carrierF _carrierG
            exact And.intro emptyCarrier emptyCarrier
          · intro F G F' G' _sameF _sameG
            exact And.intro emptyClassified emptyClassified

def FpsSingletonEmptyHistoryCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def FpsSingletonEmptyHistoryClassifier (h k : BHist) : Prop :=
  FpsSingletonEmptyHistoryCarrier h ∧ FpsSingletonEmptyHistoryCarrier k ∧ hsame h k

theorem FpsSingletonEmptyHistory_semanticNameCert :
    SemanticNameCert FpsSingletonEmptyHistoryCarrier FpsSingletonEmptyHistoryCarrier
      FpsSingletonEmptyHistoryCarrier FpsSingletonEmptyHistoryClassifier := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k same
        exact And.intro same.right.left
          (And.intro same.left (hsame_symm same.right.right))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro sameHK.left
          (And.intro sameKR.right.left
            (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro h k same _carrier
        exact same.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

theorem FpsSingletonCoeff_empty_ledger {F n : BHist} :
    FpsSingletonCarrier F ->
      hsame (FpsSingletonCoeff F n) BHist.Empty /\
        FpsSingletonClassifier (FpsSingletonCoeff F n) BHist.Empty := by
  intro _carrier
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact And.intro (hsame_refl BHist.Empty)
    (And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty)))

theorem FpsSingletonEmptyHistoryClassifier_append_split_empty_iff {p q h : BHist} :
    FpsSingletonEmptyHistoryClassifier (BEDC.FKernel.Cont.append p q) h ↔
      hsame p BHist.Empty ∧ hsame q BHist.Empty ∧ FpsSingletonEmptyHistoryCarrier h := by
  constructor
  · intro classifier
    cases classifier with
    | intro appendCarrier rest =>
        cases rest with
        | intro hCarrier _sameAppendH =>
            have splitEmpty := append_eq_empty_iff.mp appendCarrier
            exact ⟨splitEmpty.left, splitEmpty.right, hCarrier⟩
  · intro splitData
    cases splitData with
    | intro pEmpty rest =>
        cases rest with
        | intro qEmpty hCarrier =>
            have appendEmpty : hsame (BEDC.FKernel.Cont.append p q) BHist.Empty :=
              append_eq_empty_iff.mpr ⟨pEmpty, qEmpty⟩
            exact ⟨appendEmpty, hCarrier, hsame_trans appendEmpty (hsame_symm hCarrier)⟩

theorem FpsSingletonEmptyHistoryClassifier_append_pair_split_empty_iff {p q r s : BHist} :
    FpsSingletonEmptyHistoryClassifier (append p q) (append r s) ↔
      hsame p BHist.Empty ∧ hsame q BHist.Empty ∧
        hsame r BHist.Empty ∧ hsame s BHist.Empty := by
  constructor
  · intro classifier
    have leftSplit :=
      FpsSingletonEmptyHistoryClassifier_append_split_empty_iff.mp classifier
    have rightSplit := append_eq_empty_iff.mp leftSplit.right.right
    exact ⟨leftSplit.left, leftSplit.right.left, rightSplit.left, rightSplit.right⟩
  · intro splitData
    cases splitData with
    | intro pEmpty rest =>
        cases rest with
        | intro qEmpty rightData =>
            cases rightData with
            | intro rEmpty sEmpty =>
                have leftCarrier : hsame (append p q) BHist.Empty :=
                  append_eq_empty_iff.mpr ⟨pEmpty, qEmpty⟩
                have rightCarrier : hsame (append r s) BHist.Empty :=
                  append_eq_empty_iff.mpr ⟨rEmpty, sEmpty⟩
                exact
                  ⟨leftCarrier, rightCarrier,
                    hsame_trans leftCarrier (hsame_symm rightCarrier)⟩

theorem FpsSingletonEmptyHistoryClassifier_cont_split_empty {p q h : BHist} :
    Cont p q h -> FpsSingletonEmptyHistoryClassifier h BHist.Empty ->
      FpsSingletonEmptyHistoryCarrier p ∧ FpsSingletonEmptyHistoryCarrier q := by
  intro contRel classifier
  cases contRel
  have split :=
    FpsSingletonEmptyHistoryClassifier_append_split_empty_iff
      (p := p) (q := q) (h := BHist.Empty) |>.mp classifier
  exact And.intro split.left split.right.left

theorem FpsSingletonEmptyHistoryClassifier_append_component_classifiers {p q h : BHist} :
    FpsSingletonEmptyHistoryClassifier (append p q) h ->
      FpsSingletonEmptyHistoryClassifier p BHist.Empty ∧
        FpsSingletonEmptyHistoryClassifier q BHist.Empty ∧
          FpsSingletonEmptyHistoryCarrier h := by
  intro classifier
  have splitData :=
    FpsSingletonEmptyHistoryClassifier_append_split_empty_iff.mp classifier
  cases splitData with
  | intro pEmpty rest =>
      cases rest with
      | intro qEmpty hCarrier =>
          constructor
          · exact ⟨pEmpty, hsame_refl BHist.Empty, pEmpty⟩
          · constructor
            · exact ⟨qEmpty, hsame_refl BHist.Empty, qEmpty⟩
            · exact hCarrier

theorem FpsSingletonEmptyHistoryClassifier_headed_endpoint_absurd {h k : BHist} :
    FpsSingletonEmptyHistoryClassifier h k ->
      ((∃ z : BHist, h = BHist.e0 z) ∨ (∃ z : BHist, h = BHist.e1 z) ∨
        (∃ z : BHist, k = BHist.e0 z) ∨ (∃ z : BHist, k = BHist.e1 z)) -> False := by
  intro classifier headed
  have hEmpty : hsame h BHist.Empty := classifier.left
  have kEmpty : hsame k BHist.Empty := classifier.right.left
  cases headed with
  | inl leftHead =>
      cases leftHead with
      | intro z hz =>
          cases hz
          exact not_hsame_e0_empty hEmpty
  | inr rest =>
      cases rest with
      | inl leftHead =>
          cases leftHead with
          | intro z hz =>
              cases hz
              exact not_hsame_e1_empty hEmpty
      | inr rest =>
          cases rest with
          | inl rightHead =>
              cases rightHead with
              | intro z hz =>
                  cases hz
                  exact not_hsame_e0_empty kEmpty
          | inr rightHead =>
              cases rightHead with
              | intro z hz =>
                  cases hz
                  exact not_hsame_e1_empty kEmpty

theorem FpsSingletonEmptyHistoryClassifier_continuation_comm_closed
    {F G left right : BHist} :
    FpsSingletonEmptyHistoryCarrier F -> FpsSingletonEmptyHistoryCarrier G ->
      Cont F G left -> Cont G F right -> FpsSingletonEmptyHistoryCarrier left ∧
        FpsSingletonEmptyHistoryCarrier right ∧
          FpsSingletonEmptyHistoryClassifier left right := by
  intro carrierF carrierG leftCont rightCont
  cases carrierF
  cases carrierG
  cases leftCont
  cases rightCont
  have emptyCarrier : FpsSingletonEmptyHistoryCarrier BHist.Empty := hsame_refl BHist.Empty
  exact And.intro emptyCarrier
    (And.intro emptyCarrier
      (And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))))

end BEDC.Derived.FpsUp
