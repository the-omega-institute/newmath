import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem TrialDiv_unit_step_result_not_unit {b n b' : BHist} :
    TrialDiv b n ->
      Cont b (BHist.e1 BHist.Empty) b' ->
        hsame b' (BHist.e1 BHist.Empty) -> False := by
  intro trial step resultUnit
  have displayed : Cont b (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    cont_result_hsame_transport step resultUnit
  have emptyBound : hsame b BHist.Empty :=
    cont_right_cancel displayed (cont_left_unit (BHist.e1 BHist.Empty))
  exact TrialDiv_bound_not_empty trial emptyBound

end BEDC.Derived.PrimeUp
