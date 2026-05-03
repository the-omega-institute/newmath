import BEDC.Derived.AdjunctionUp
import BEDC.Derived.CategoryUp.Cycle
import BEDC.FKernel.NameCert

namespace BEDC.Derived.EquivCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.AdjunctionUp
open BEDC.Derived.CategoryUp
open BEDC.Derived.NatTransUp

theorem EquivCatAdjunction_empty_roundtrip_identity_components
    {p q a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty ->
        NatTransPrefixComponentCarrier p q a BHist.Empty ∧
          NatTransPrefixComponentCarrier q p a BHist.Empty := by
  intro carrier leftEmpty rightEmpty
  have unitCounitEmpty : unit = BHist.Empty ∧ counit = BHist.Empty := by
    cases leftEmpty
    exact cont_empty_result_inversion carrier.right.right.left
  have counitUnitEmpty : counit = BHist.Empty ∧ unit = BHist.Empty := by
    cases rightEmpty
    exact cont_empty_result_inversion carrier.right.right.right
  cases unitCounitEmpty.left
  cases unitCounitEmpty.right
  cases counitUnitEmpty.left
  cases counitUnitEmpty.right
  exact And.intro carrier.left carrier.right.left

theorem EquivCatAdjunction_empty_roundtrip_prefix_determinacy
    {p q a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty ->
        hsame p q ∧ hsame unit BHist.Empty ∧ hsame counit BHist.Empty ∧
          NatTransPrefixComponentCarrier p q a BHist.Empty ∧
            NatTransPrefixComponentCarrier q p a BHist.Empty := by
  intro carrier leftEmpty rightEmpty
  have emptyComponents :
      NatTransPrefixComponentCarrier p q a BHist.Empty ∧
        NatTransPrefixComponentCarrier q p a BHist.Empty :=
    EquivCatAdjunction_empty_roundtrip_identity_components carrier leftEmpty rightEmpty
  have prefixData :=
    Iff.mp NatTransPrefixComponentCarrier_empty_identity_iff emptyComponents.left
  have unitCounitEmpty : unit = BHist.Empty ∧ counit = BHist.Empty := by
    cases leftEmpty
    exact cont_empty_result_inversion carrier.right.right.left
  exact And.intro prefixData.right.right.right
    (And.intro unitCounitEmpty.left
      (And.intro unitCounitEmpty.right
        (And.intro emptyComponents.left emptyComponents.right)))

theorem EquivCatAdjunction_empty_roundtrip_zero_source_absurd
    {tail q a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier (BHist.e0 tail) q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty -> False := by
  intro carrier leftEmpty rightEmpty
  have components :=
    EquivCatAdjunction_empty_roundtrip_identity_components carrier leftEmpty rightEmpty
  exact NatTransPrefixComponentCarrier_zero_headed_component_absurd components.left
    (Or.inl (Exists.intro tail rfl))

theorem EquivCatAdjunction_empty_roundtrip_zero_target_absurd
    {p tail a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p (BHist.e0 tail) a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty -> False := by
  intro carrier leftEmpty rightEmpty
  have components :=
    EquivCatAdjunction_empty_roundtrip_identity_components carrier leftEmpty rightEmpty
  exact NatTransPrefixComponentCarrier_zero_headed_component_absurd components.right
    (Or.inl (Exists.intro tail rfl))

theorem EquivCatAdjunction_empty_roundtrip_e1_source_target_eq
    {tail q a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier (BHist.e1 tail) q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty -> q = BHist.e1 tail := by
  intro carrier leftEmpty rightEmpty
  have components :=
    EquivCatAdjunction_empty_roundtrip_identity_components carrier leftEmpty rightEmpty
  have componentData :=
    (NatTransPrefixComponentCarrier_e1_source_empty_component_iff
      (p := tail) (q := q) (a := a)).mp components.left
  exact componentData.right.right

theorem EquivCatAdjunction_empty_roundtrip_target_prefix_deterministic
    {p q r a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty ->
        NatTransPrefixComponentCarrier p r a BHist.Empty -> hsame q r := by
  intro carrier leftEmpty rightEmpty displayed
  have emptyComponents :
      NatTransPrefixComponentCarrier p q a BHist.Empty ∧
        NatTransPrefixComponentCarrier q p a BHist.Empty :=
    EquivCatAdjunction_empty_roundtrip_identity_components carrier leftEmpty rightEmpty
  exact NatTransPrefixComponentCarrier_empty_identity_prefix_trans emptyComponents.right displayed

theorem EquivCatAdjunction_empty_roundtrip_source_prefix_deterministic
    {p q r a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty ->
        NatTransPrefixComponentCarrier r q a BHist.Empty -> hsame p r := by
  intro carrier leftEmpty rightEmpty displayed
  have emptyComponents :
      NatTransPrefixComponentCarrier p q a BHist.Empty ∧
        NatTransPrefixComponentCarrier q p a BHist.Empty :=
    EquivCatAdjunction_empty_roundtrip_identity_components carrier leftEmpty rightEmpty
  have sameRP : hsame r p :=
    NatTransPrefixComponentCarrier_empty_identity_prefix_trans displayed emptyComponents.right
  exact hsame_symm sameRP

theorem EquivCatCycleIdentityCarrier_semanticNameCert {a b f g : BHist}
    (left : CategoryHomCarrier a b f) (right : CategoryHomCarrier b a g) :
    SemanticNameCert
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier b a g ∧ hsame t BHist.Empty ∧
          hsame g BHist.Empty)
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier b a g ∧ hsame t BHist.Empty ∧
          hsame g BHist.Empty)
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier b a g ∧ hsame t BHist.Empty ∧
          hsame g BHist.Empty)
      hsame := by
  have cycle := CategoryHomCarrier_cycle_tails_empty left right
  constructor
  · constructor
    · exact Exists.intro BHist.Empty
        (And.intro
          (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b)
            cycle.right.left left)
          (And.intro right (And.intro (hsame_refl BHist.Empty) cycle.right.right)))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) same carrier.left)
        (And.intro carrier.right.left
          (And.intro (hsame_trans (hsame_symm same) carrier.right.right.left)
            carrier.right.right.right))
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.EquivCatUp
