import BEDC.FKernel.Cont
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_left_unit_law_result_not_empty {u d r : BHist} :
    (∀ {x y : BHist}, RatHistoryCarrier x -> Cont u x y -> RatHistoryClassifier y x) ->
      RatHistoryCarrier d -> Cont u d r -> hsame r BHist.Empty -> False := by
  intro leftLaw carrierD contUDR resultEmpty
  have classified : RatHistoryClassifier r d := leftLaw carrierD contUDR
  exact RatHistoryCarrier_not_empty classified.left resultEmpty

end BEDC.Derived.FieldUp
