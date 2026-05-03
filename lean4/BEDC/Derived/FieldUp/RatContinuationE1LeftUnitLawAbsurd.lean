import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_e1_left_unit_law_absurd {tail : BHist} :
    ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont (BHist.e1 tail) d r ->
      RatHistoryClassifier r d) -> False) := by
  intro leftUnit
  have endpointEmpty : hsame (BHist.e1 tail) BHist.Empty :=
    field_rat_denominator_continuation_left_unit_law_endpoint_empty_iff.mp leftUnit
  exact not_hsame_e1_empty endpointEmpty

end BEDC.Derived.FieldUp
