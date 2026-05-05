import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

def FieldExtRatReflexiveCarrier (h : BHist) : Prop :=
  RatHistoryCarrier h ∧ RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
    Cont BHist.Empty h (FieldExtSingletonEmbedding h)

theorem FieldExtRatReflexiveCarrier_rat_history_closure {h : BHist} :
    RatHistoryCarrier h -> FieldExtRatReflexiveCarrier h := by
  intro carrier
  have embeddedCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding h) := by
    unfold FieldExtSingletonEmbedding
    exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left h)) carrier
  have identityContinuation : Cont BHist.Empty h (FieldExtSingletonEmbedding h) := by
    unfold FieldExtSingletonEmbedding
    exact cont_intro rfl
  exact And.intro carrier (And.intro embeddedCarrier identityContinuation)

end BEDC.Derived.FieldExtUp
