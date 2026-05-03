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

theorem MonadAdjunctionEndomorphism_parallel_triangle_suffix_same
    {p a unit counit left right suffix left' right' : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      Cont left suffix left' -> Cont right suffix right' -> hsame left' right' := by
  intro carrier leftCont rightCont
  have triangleEmpty :=
    MonadAdjunctionEndomorphism_triangle_results_empty (p := p) (a := a) (unit := unit)
      (counit := counit) (left := left) (right := right) carrier
  have sameSource : hsame left right :=
    hsame_trans triangleEmpty.left (hsame_symm triangleEmpty.right)
  exact cont_respects_hsame sameSource (hsame_refl suffix) leftCont rightCont

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

theorem MonadAdjunctionEndomorphism_triangle_composite_empty
    {p a unit counit left right composite : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right -> Cont left right composite ->
      hsame composite BHist.Empty := by
  intro carrier compositeRel
  have triangleEmpty :=
    MonadAdjunctionEndomorphism_triangle_results_empty carrier
  exact cont_respects_hsame triangleEmpty.left triangleEmpty.right compositeRel
    (cont_right_unit BHist.Empty)

theorem MonadAdjunctionEndomorphism_unit_counit_triangle_empty
    {p a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      hsame unit BHist.Empty ∧ hsame counit BHist.Empty ∧
        hsame left BHist.Empty ∧ hsame right BHist.Empty := by
  intro carrier
  have unitEmpty : hsame unit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.left).right.right.right
  have counitEmpty : hsame counit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.right.left).right.right.right
  have triangleEmpty :
      hsame left BHist.Empty ∧ hsame right BHist.Empty :=
    MonadAdjunctionEndomorphism_triangle_results_empty carrier
  exact And.intro unitEmpty (And.intro counitEmpty triangleEmpty)

theorem MonadAdjunctionEndomorphism_left_triangle_result_empty_suffix_empty
    {p a unit counit left right suffix out : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      Cont left suffix out -> hsame out BHist.Empty -> hsame suffix BHist.Empty := by
  intro carrier leftSuffix outEmpty
  have leftEmpty : hsame left BHist.Empty :=
    (MonadAdjunctionEndomorphism_triangle_results_empty carrier).left
  cases leftEmpty
  cases outEmpty
  exact (cont_empty_result_inversion leftSuffix).right

theorem MonadAdjunctionEndomorphism_triangle_bridge_empty_iff
    {p a unit counit left right bridge : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      (Cont left bridge right ↔ hsame bridge BHist.Empty) := by
  intro carrier
  constructor
  · intro bridgeCont
    exact
      MonadAdjunctionEndomorphism_left_triangle_result_empty_suffix_empty
        carrier bridgeCont (MonadAdjunctionEndomorphism_triangle_results_empty carrier).right
  · intro bridgeEmpty
    have leftEmpty : hsame left BHist.Empty :=
      (MonadAdjunctionEndomorphism_triangle_results_empty carrier).left
    have rightEmpty : hsame right BHist.Empty :=
      (MonadAdjunctionEndomorphism_triangle_results_empty carrier).right
    cases leftEmpty
    cases bridgeEmpty
    cases rightEmpty
    exact cont_right_unit BHist.Empty

end BEDC.Derived.MonadUp
