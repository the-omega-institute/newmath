import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatHistoryClassifier_append_right_carrier_absurd {d u : BHist} :
    RatHistoryCarrier u -> RatHistoryClassifier (append d u) d -> False := by
  intro carrierU classified
  have canonicalContinuation : Cont d u (append d u) := cont_intro rfl
  have collapsedContinuation : Cont d u d :=
    cont_result_hsame_transport canonicalContinuation classified.right.right
  exact RatHistoryCarrier_not_empty carrierU (cont_right_unit_unique collapsedContinuation)

theorem RatHistoryClassifier_append_left_carrier_absurd {u d : BHist} :
    RatHistoryCarrier u -> RatHistoryClassifier (append u d) d -> False := by
  intro carrierU classified
  have canonicalContinuation : Cont u d (append u d) := cont_intro rfl
  have collapsedContinuation : Cont u d d :=
    cont_result_hsame_transport canonicalContinuation classified.right.right
  exact RatHistoryCarrier_not_empty carrierU (cont_left_unit_unique collapsedContinuation)

end BEDC.Derived.FieldUp
