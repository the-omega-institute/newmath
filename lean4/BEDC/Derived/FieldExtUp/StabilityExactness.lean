import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem FieldExtRatReflexive_stability_exactness_obligations {h h' k k' r r' : BHist} :
    RatHistoryClassifier h h' -> RatHistoryClassifier k k' ->
      Cont (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) r ->
        Cont h' k' r' ->
          RatHistoryClassifier (FieldExtSingletonEmbedding h) h ∧
            RatHistoryClassifier (FieldExtSingletonEmbedding k) k ∧
              RatHistoryClassifier r r' := by
  intro classifiedH classifiedK leftContinuation rightContinuation
  have embeddedH := FieldExtRatReflexiveEmbedding_classifier_endpoint_package classifiedH
  have embeddedK := FieldExtRatReflexiveEmbedding_classifier_endpoint_package classifiedK
  have scalarCompatible :
      RatHistoryClassifier r r' :=
    FieldExtRatReflexiveVectorSpace_scalar_action_congruence
      classifiedH classifiedK leftContinuation rightContinuation
  exact And.intro embeddedH.left (And.intro embeddedK.left scalarCompatible)

end BEDC.Derived.FieldExtUp
