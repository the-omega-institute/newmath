import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_two_sided_unit_law_endpoint_empty_iff {u : BHist} :
    (((forall {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ∧
        (forall {d r : BHist}, RatHistoryCarrier d -> Cont u d r ->
          RatHistoryClassifier r d)) <->
      hsame u BHist.Empty) := by
  constructor
  · intro laws
    exact field_rat_denominator_continuation_right_unit_law_endpoint_empty_iff.mp laws.left
  · intro endpointEmpty
    exact And.intro
      (field_rat_denominator_continuation_right_unit_law_endpoint_empty_iff.mpr endpointEmpty)
      (field_rat_denominator_continuation_left_unit_law_endpoint_empty_iff.mpr endpointEmpty)

end BEDC.Derived.FieldUp
