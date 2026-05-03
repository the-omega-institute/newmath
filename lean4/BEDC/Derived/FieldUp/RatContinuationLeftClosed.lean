import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatHistoryClassifier_continuation_left_closed {e d d' r r' : BHist} :
    RatHistoryCarrier e -> RatHistoryClassifier d d' -> Cont e d r -> Cont e d' r' ->
      RatHistoryClassifier r r' := by
  intro carrierE classified leftContinuation rightContinuation
  have carrierR : RatHistoryCarrier r :=
    RatHistoryCarrier_continuation_closed carrierE classified.left leftContinuation
  have carrierR' : RatHistoryCarrier r' :=
    RatHistoryCarrier_continuation_closed carrierE classified.right.left rightContinuation
  have sameResult : hsame r r' :=
    cont_respects_hsame (hsame_refl e) classified.right.right leftContinuation rightContinuation
  exact ⟨carrierR, carrierR', sameResult⟩

end BEDC.Derived.FieldUp
