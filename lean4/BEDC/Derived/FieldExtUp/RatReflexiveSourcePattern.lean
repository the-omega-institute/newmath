import BEDC.Derived.FieldExtUp.RatReflexiveOperationTable

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.FieldUp
open BEDC.Derived.RatUp

theorem FieldExtRatReflexive_source_pattern_classifier_obligations {h k r m out : BHist} :
    RatHistoryClassifier h k -> RatHistoryCarrier r -> RatHistoryCarrier m ->
      Cont (FieldExtSingletonEmbedding r) m out ->
        RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
          RatHistoryCarrier (FieldExtSingletonEmbedding k) ∧
            RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) ∧
              Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
                Cont BHist.Empty k (FieldExtSingletonEmbedding k) ∧ RatHistoryCarrier out := by
  intro classified carrierR carrierM actionCont
  have lock :
      RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
        RatHistoryCarrier (FieldExtSingletonEmbedding k) ∧
          RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) ∧
            Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
              Cont BHist.Empty k (FieldExtSingletonEmbedding k) :=
    FieldExtRatReflexive_source_pattern_lock classified
  have embeddedR : RatHistoryCarrier (FieldExtSingletonEmbedding r) := by
    unfold FieldExtSingletonEmbedding
    exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left r)) carrierR
  have outCarrier : RatHistoryCarrier out :=
    RatHistoryCarrier_continuation_closed embeddedR carrierM actionCont
  exact And.intro lock.left
    (And.intro lock.right.left
      (And.intro lock.right.right.left
        (And.intro lock.right.right.right.left
          (And.intro lock.right.right.right.right outCarrier))))

end BEDC.Derived.FieldExtUp
