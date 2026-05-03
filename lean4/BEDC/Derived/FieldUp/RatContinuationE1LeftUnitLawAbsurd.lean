import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_e1_left_unit_law_absurd {tail : BHist} :
    ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont (BHist.e1 tail) d r ->
      RatHistoryClassifier r d) -> False) := by
  intro leftUnit
  have endpointEmpty : hsame (BHist.e1 tail) BHist.Empty :=
    field_rat_denominator_continuation_left_unit_law_endpoint_empty_iff.mp leftUnit
  exact not_hsame_e1_empty endpointEmpty

theorem field_rat_denominator_continuation_right_unit_law_visible_endpoint_absurd {u p : BHist} :
    (∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ->
      (hsame u (BHist.e0 p) -> False) ∧ (hsame u (BHist.e1 p) -> False) := by
  intro rightUnit
  have carrierD1 : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have canonicalContinuation : Cont (BHist.e1 BHist.Empty) u
      (append (BHist.e1 BHist.Empty) u) :=
    cont_intro rfl
  have classifiedResult :
      RatHistoryClassifier (append (BHist.e1 BHist.Empty) u) (BHist.e1 BHist.Empty) :=
    rightUnit carrierD1 canonicalContinuation
  have collapsedContinuation : Cont (BHist.e1 BHist.Empty) u (BHist.e1 BHist.Empty) :=
    cont_result_hsame_transport canonicalContinuation classifiedResult.right.right
  have endpointEmpty : hsame u BHist.Empty := cont_right_unit_unique collapsedContinuation
  constructor
  · intro sameVisible
    exact not_hsame_e0_empty (hsame_trans (hsame_symm sameVisible) endpointEmpty)
  · intro sameVisible
    exact not_hsame_e1_empty (hsame_trans (hsame_symm sameVisible) endpointEmpty)

end BEDC.Derived.FieldUp
