import BEDC.Derived.FieldExtUp.RatReflexiveEmbedding
import BEDC.Derived.FieldExtUp.RatReflexiveOperationTable
import BEDC.Derived.FieldExtUp.RatReflexiveSourcePattern
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

def NumFieldRatReflexiveCarrier (h : BHist) : Prop :=
  RatHistoryCarrier h ∧ RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
    Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
      RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h)

theorem NumFieldRatReflexive_finite_basis_witness {h : BHist} :
    NumFieldRatReflexiveCarrier h ->
      RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
        Cont h (BHist.e1 BHist.Empty) (append h (BHist.e1 BHist.Empty)) ∧
          RatHistoryClassifier (append h (BHist.e1 BHist.Empty))
            (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) := by
  intro carrier
  have basisCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have basisContinuation : Cont h (BHist.e1 BHist.Empty) (append h (BHist.e1 BHist.Empty)) :=
    cont_intro rfl
  have sourceClassified : RatHistoryClassifier h (FieldExtSingletonEmbedding h) :=
    RatHistoryLedgerPolicy_raw_visible_classifier carrier.right.right.right
  have appendedClassified :
      RatHistoryClassifier (append h (BHist.e1 BHist.Empty))
        (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) :=
    RatHistoryClassifier_append_unary_denominator_closed sourceClassified
      (unary_e1_closed unary_empty) (hsame_refl (BHist.e1 BHist.Empty))
  exact And.intro basisCarrier (And.intro basisContinuation appendedClassified)

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

end BEDC.Derived.NumFieldUp
