import BEDC.Derived.FieldExtUp.RatReflexiveSourcePattern

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

def NumFieldRatReflexiveCarrier (h : BHist) : Prop :=
  RatHistoryCarrier h ∧ RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
    RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
      Cont BHist.Empty h (FieldExtSingletonEmbedding h)

def NumFieldRatReflexiveClassifier (h k : BHist) : Prop :=
  NumFieldRatReflexiveCarrier h ∧ NumFieldRatReflexiveCarrier k ∧ RatHistoryClassifier h k

theorem NumFieldReflexiveRational_finite_extension_witness {m coord : BHist} :
    RatHistoryCarrier m -> Cont m BHist.Empty coord ->
      RatHistoryClassifier coord m ∧ RatHistoryCarrier (FieldExtSingletonEmbedding m) ∧
        RatHistoryClassifier (FieldExtSingletonEmbedding m) m := by
  intro carrierM coordinateReadback
  have sameCoordM : hsame coord m :=
    cont_right_unit_result coordinateReadback
  have coordCarrier : RatHistoryCarrier coord :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameCoordM) carrierM
  have coordClassifier : RatHistoryClassifier coord m :=
    And.intro coordCarrier (And.intro carrierM sameCoordM)
  have embeddedCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding m) := by
    unfold FieldExtSingletonEmbedding
    exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left m)) carrierM
  have embeddedClassifier : RatHistoryClassifier (FieldExtSingletonEmbedding m) m := by
    unfold FieldExtSingletonEmbedding
    exact And.intro embeddedCarrier (And.intro carrierM (append_empty_left m))
  exact And.intro coordClassifier (And.intro embeddedCarrier embeddedClassifier)

theorem NumFieldRatReflexive_carrier_classifier {h k : BHist} :
    RatHistoryClassifier h k ->
      NumFieldRatReflexiveCarrier h ∧ NumFieldRatReflexiveCarrier k ∧
        NumFieldRatReflexiveClassifier h k ∧
          Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
            Cont BHist.Empty k (FieldExtSingletonEmbedding k) ∧
              RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) := by
  intro classified
  have locked := FieldExtRatReflexiveEmbedding_ledger_source_lock classified
  have hCarrier : NumFieldRatReflexiveCarrier h :=
    And.intro classified.left
      (And.intro locked.right.right.left.left
        (And.intro locked.left locked.right.right.right.left))
  have kCarrier : NumFieldRatReflexiveCarrier k :=
    And.intro classified.right.left
      (And.intro locked.right.right.left.right.left
        (And.intro locked.right.left locked.right.right.right.right))
  have numClassifier : NumFieldRatReflexiveClassifier h k :=
    And.intro hCarrier (And.intro kCarrier classified)
  exact And.intro hCarrier
    (And.intro kCarrier
      (And.intro numClassifier
        (And.intro locked.right.right.right.left
          (And.intro locked.right.right.right.right locked.right.right.left))))

theorem NumFieldReflexiveRational_namecert_obligation_package :
    SemanticNameCert NumFieldRatReflexiveCarrier NumFieldRatReflexiveCarrier
      NumFieldRatReflexiveCarrier NumFieldRatReflexiveClassifier ∧
      (forall {h k : BHist}, RatHistoryClassifier h k ->
        NumFieldRatReflexiveClassifier h k) ∧
      (forall {h k : BHist}, NumFieldRatReflexiveClassifier h k ->
        RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k)) := by
  have ratCert :
      SemanticNameCert RatHistoryCarrier RatHistoryCarrier RatHistoryCarrier
        RatHistoryClassifier :=
    rat_history_semantic_name_certificate
  have semantic :
      SemanticNameCert NumFieldRatReflexiveCarrier NumFieldRatReflexiveCarrier
        NumFieldRatReflexiveCarrier NumFieldRatReflexiveClassifier := {
    core := {
      carrier_inhabited := by
        cases ratCert.core.carrier_inhabited with
        | intro h carrier =>
            exact Exists.intro h
              (NumFieldRatReflexive_carrier_classifier
                (ratCert.core.equiv_refl carrier)).left
      equiv_refl := by
        intro h carrier
        exact And.intro carrier
          (And.intro carrier (ratCert.core.equiv_refl carrier.left))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (ratCert.core.equiv_symm classified.right.right))
      equiv_trans := by
        intro h k r hk kr
        exact And.intro hk.left
          (And.intro kr.right.left
            (ratCert.core.equiv_trans hk.right.right kr.right.right))
      carrier_respects_equiv := by
        intro h k classified carrierH
        exact (NumFieldRatReflexive_carrier_classifier classified.right.right).right.left
    }
    pattern_sound := by
      intro h carrier
      exact (NumFieldRatReflexive_carrier_classifier
        (ratCert.core.equiv_refl carrier.left)).left
    ledger_sound := by
      intro h carrier
      exact (NumFieldRatReflexive_carrier_classifier
        (ratCert.core.equiv_refl carrier.left)).left
  }
  exact And.intro semantic
    (And.intro
      (by
        intro h k classified
        exact (NumFieldRatReflexive_carrier_classifier classified).right.right.left)
      (by
        intro h k classified
        exact (NumFieldRatReflexive_carrier_classifier classified.right.right).right.right.right.right.right))

end BEDC.Derived.NumFieldUp
