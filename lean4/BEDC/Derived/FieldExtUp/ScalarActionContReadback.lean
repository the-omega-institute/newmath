import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp
open BEDC.Derived.RatUp

theorem FieldExtRatReflexiveEmbedding_scalar_action_cont_readback {r m out : BHist} :
    RatHistoryCarrier r -> RatHistoryCarrier m -> Cont r m out ->
      RatHistoryClassifier (append BHist.Empty out) out := by
  intro carrierR carrierM continuation
  have carrierOut : RatHistoryCarrier out :=
    RatHistoryCarrier_continuation_closed carrierR carrierM continuation
  have embeddedCarrier : RatHistoryCarrier (append BHist.Empty out) :=
    RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left out)) carrierOut
  exact And.intro embeddedCarrier (And.intro carrierOut (append_empty_left out))

end BEDC.Derived.FieldExtUp
