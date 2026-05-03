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

theorem MonadAdjunctionEndomorphism_triangle_composite_empty
    {p a unit counit left right composite : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right -> Cont left right composite ->
      hsame composite BHist.Empty := by
  intro carrier compositeRel
  have triangleEmpty :=
    MonadAdjunctionEndomorphism_triangle_results_empty carrier
  exact cont_respects_hsame triangleEmpty.left triangleEmpty.right compositeRel
    (cont_right_unit BHist.Empty)

end BEDC.Derived.MonadUp
