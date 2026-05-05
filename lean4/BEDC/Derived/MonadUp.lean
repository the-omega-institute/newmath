import BEDC.Derived.AdjunctionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
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

theorem MonadAdjunctionEndomorphism_right_triangle_result_empty_suffix_empty
    {p a unit counit left right suffix out : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      Cont right suffix out -> hsame out BHist.Empty -> hsame suffix BHist.Empty := by
  intro carrier rightSuffix outEmpty
  have rightEmpty : hsame right BHist.Empty :=
    (MonadAdjunctionEndomorphism_triangle_results_empty carrier).right
  cases rightEmpty
  cases outEmpty
  exact (cont_empty_result_inversion rightSuffix).right

theorem MonadAdjunctionEndomorphism_unit_counit_bridge_empty_iff
    {p a unit counit left right bridge : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      (Cont unit bridge counit ↔ hsame bridge BHist.Empty) := by
  intro carrier
  constructor
  · intro bridgeCont
    exact MonadAdjunctionEndomorphism_middle_between_unit_counit_empty carrier bridgeCont
  · intro bridgeEmpty
    have componentEmpty :=
      MonadAdjunctionEndomorphism_unit_counit_triangle_empty carrier
    have unitEmpty : hsame unit BHist.Empty := componentEmpty.left
    have counitEmpty : hsame counit BHist.Empty := componentEmpty.right.left
    cases unitEmpty
    cases bridgeEmpty
    cases counitEmpty
    exact cont_right_unit BHist.Empty

theorem MonadAdjunctionEndomorphism_left_triangle_suffix_output_empty_iff
    {p a unit counit left right suffix out : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      Cont left suffix out -> (hsame out BHist.Empty ↔ hsame suffix BHist.Empty) := by
  intro carrier leftSuffix
  constructor
  · intro outEmpty
    exact
      MonadAdjunctionEndomorphism_left_triangle_result_empty_suffix_empty
        carrier leftSuffix outEmpty
  · intro suffixEmpty
    have leftEmpty : hsame left BHist.Empty :=
      (MonadAdjunctionEndomorphism_triangle_results_empty carrier).left
    exact
      cont_respects_hsame leftEmpty suffixEmpty leftSuffix
        (cont_right_unit BHist.Empty)

theorem MonadAdjunctionEndomorphism_semanticNameCert {p a : BHist}
    (pUnary : UnaryHistory p) (aUnary : UnaryHistory a) :
    let Carrier : BHist -> Prop :=
      fun unit : BHist => ∃ counit left right : BHist,
        AdjunctionUnitCounitCarrier p p a unit counit left right
    SemanticNameCert Carrier Carrier Carrier hsame := by
  intro Carrier
  constructor
  · constructor
    · have emptyCarrier :
          AdjunctionUnitCounitCarrier p p a BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty :=
        (AdjunctionUnitCounitCarrier_empty_components_iff (p := p) (q := p) (a := a)
          (left := BHist.Empty) (right := BHist.Empty)).mpr
          (And.intro pUnary
            (And.intro pUnary
              (And.intro aUnary
                (And.intro (hsame_refl p)
                  (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))))))
      exact
        Exists.intro BHist.Empty
          (Exists.intro BHist.Empty (Exists.intro BHist.Empty
            (Exists.intro BHist.Empty emptyCarrier)))
    · intro unit _carrier
      exact hsame_refl unit
    · intro unit unit' sameUnit
      exact hsame_symm sameUnit
    · intro unit unit' unit'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro unit unit' sameUnit carrier
      cases carrier with
      | intro counit carrierRest =>
          cases carrierRest with
          | intro left carrierRest =>
              cases carrierRest with
              | intro right displayCarrier =>
                  cases sameUnit
                  exact Exists.intro counit (Exists.intro left (Exists.intro right displayCarrier))
  · intro unit source
    exact source
  · intro unit source
    exact source

end BEDC.Derived.MonadUp
