import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.MonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.AdjunctionUp
open BEDC.Derived.NatTransUp

theorem MonadAdjunctionEndomorphism_triangle_results_empty
    {p a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      hsame left BHist.Empty ∧ hsame right BHist.Empty := by
  intro carrier
  have unitEmpty : hsame unit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.left).right.right.right
  have counitEmpty : hsame counit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.right.left).right.right.right
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame unitEmpty counitEmpty carrier.right.right.left
      (cont_right_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame counitEmpty unitEmpty carrier.right.right.right
      (cont_right_unit BHist.Empty)
  exact And.intro leftEmpty rightEmpty

theorem MonadAdjunctionEndomorphism_middle_between_unit_counit_empty
    {p a unit counit left right bridge : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      Cont unit bridge counit -> hsame bridge BHist.Empty := by
  intro carrier bridgeCont
  have unitEmpty : hsame unit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.left).right.right.right
  have counitEmpty : hsame counit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.right.left).right.right.right
  cases unitEmpty
  cases counitEmpty
  exact (cont_empty_result_inversion bridgeCont).right

theorem MonadAdjunctionEndomorphism_middle_between_counit_unit_empty
    {p a unit counit left right bridge : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      Cont counit bridge unit -> hsame bridge BHist.Empty := by
  intro carrier bridgeCont
  have unitEmpty : hsame unit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.left).right.right.right
  have counitEmpty : hsame counit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.right.left).right.right.right
  cases unitEmpty
  cases counitEmpty
  exact (cont_empty_result_inversion bridgeCont).right

end BEDC.Derived.MonadUp
