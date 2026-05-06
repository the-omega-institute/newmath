import BEDC.FKernel.Cont

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MeasureZeroBHist_carrier_classifier_stability
    {h k event event' endpoint endpoint' : BHist} :
    hsame h BHist.Empty -> hsame h k -> hsame event BHist.Empty ->
      hsame event event' -> Cont BHist.Empty BHist.Empty endpoint ->
        Cont BHist.Empty BHist.Empty endpoint' ->
          hsame k BHist.Empty ∧ hsame event' BHist.Empty ∧ hsame endpoint endpoint' := by
  intro histEmpty sameHist eventEmpty sameEvent endpointCont endpointCont'
  have targetHistEmpty : hsame k BHist.Empty :=
    hsame_trans (hsame_symm sameHist) histEmpty
  have targetEventEmpty : hsame event' BHist.Empty :=
    hsame_trans (hsame_symm sameEvent) eventEmpty
  have endpointsSame : hsame endpoint endpoint' :=
    cont_deterministic endpointCont endpointCont'
  exact And.intro targetHistEmpty (And.intro targetEventEmpty endpointsSame)

theorem MeasureCountableZeroTail_canonical {tail endpoint : BHist} :
    Cont BHist.Empty BHist.Empty tail -> Cont tail BHist.Empty endpoint ->
      hsame tail BHist.Empty ∧ hsame endpoint BHist.Empty ∧ hsame endpoint tail := by
  intro tailCont endpointCont
  have tailEmpty : hsame tail BHist.Empty :=
    cont_left_unit_result tailCont
  have endpointTail : hsame endpoint tail :=
    cont_deterministic endpointCont (cont_right_unit tail)
  have endpointEmpty : hsame endpoint BHist.Empty :=
    hsame_trans endpointTail tailEmpty
  exact And.intro tailEmpty (And.intro endpointEmpty endpointTail)

end BEDC.Derived.MeasureUp
