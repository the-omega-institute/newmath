import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatHistoryClassifier_continuation_tail_iff {d e r : BHist} :
    RatHistoryCarrier d -> RatHistoryCarrier e ->
      (Cont d e r <-> RatHistoryClassifier r (append d e)) := by
  intro carrierD carrierE
  constructor
  · intro continuation
    have carrierR : RatHistoryCarrier r :=
      RatHistoryCarrier_continuation_closed carrierD carrierE continuation
    have carrierAppend : RatHistoryCarrier (append d e) :=
      RatHistoryCarrier_continuation_closed carrierD carrierE (cont_intro rfl)
    exact ⟨carrierR, carrierAppend, cont_deterministic continuation (cont_intro rfl)⟩
  · intro classified
    exact classified.right.right

end BEDC.Derived.FieldUp
