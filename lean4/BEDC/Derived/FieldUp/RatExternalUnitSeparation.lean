import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_external_unit_separation_package {u : BHist} :
    (((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ↔
        hsame u BHist.Empty) ∧
      ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ↔
        hsame u BHist.Empty) ∧
      (RatHistoryCarrier u ->
        ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ->
          False) ∧
          ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ->
            False))) := by
  constructor
  · exact field_rat_denominator_continuation_right_unit_law_endpoint_empty_iff
  · constructor
    · exact field_rat_denominator_continuation_left_unit_law_endpoint_empty_iff
    · intro carrierU
      constructor
      · intro rightUnit
        exact field_rat_denominator_continuation_no_internal_unit carrierU rightUnit
      · intro leftUnit
        exact field_rat_denominator_continuation_no_internal_left_unit carrierU leftUnit

end BEDC.Derived.FieldUp
