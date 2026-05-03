import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_no_one_sided_internal_unit {u : BHist} :
    RatHistoryCarrier u ->
      ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ->
          False) ∧
        ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ->
          False) := by
  intro carrierU
  constructor
  · intro rightUnitLaw
    exact field_rat_denominator_continuation_no_internal_unit carrierU rightUnitLaw
  · intro leftUnitLaw
    exact field_rat_denominator_continuation_no_internal_left_unit carrierU leftUnitLaw

end BEDC.Derived.FieldUp
