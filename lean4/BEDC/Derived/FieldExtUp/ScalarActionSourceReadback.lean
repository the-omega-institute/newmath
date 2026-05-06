import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem FieldExtRatReflexive_embedded_scalar_action_source_readback {h k out : BHist} :
    RatHistoryClassifier h k ->
      Cont (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) out ->
        RatHistoryClassifier out (append h k) := by
  intro classified embeddedAction
  have sourceH : RatHistoryClassifier h h :=
    And.intro classified.left (And.intro classified.left (hsame_refl h))
  have sourceK : RatHistoryClassifier k k :=
    And.intro classified.right.left (And.intro classified.right.left (hsame_refl k))
  have sourceAction : Cont h k (append h k) := cont_intro rfl
  exact FieldExtRatReflexiveVectorSpace_scalar_action_congruence
    sourceH sourceK embeddedAction sourceAction

end BEDC.Derived.FieldExtUp
