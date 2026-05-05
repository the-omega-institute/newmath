import BEDC.Derived.AdjunctionUp
import BEDC.Derived.CategoryUp.Cycle
import BEDC.FKernel.NameCert

namespace BEDC.Derived.EquivCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
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

theorem EquivCatAdjunction_empty_roundtrip_e1_prefix_tail_hsame
    {sourceTail targetTail a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier (BHist.e1 sourceTail) (BHist.e1 targetTail) a unit counit
      left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty ->
        hsame sourceTail targetTail := by
  intro carrier leftEmpty rightEmpty
  have prefixes :=
    EquivCatAdjunction_empty_roundtrip_prefix_determinacy carrier leftEmpty rightEmpty
  exact hsame_e1_iff.mp prefixes.left

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

theorem EquivCatAdjunction_empty_roundtrip_unit_counit_empty_iff
    {p q a unit counit left right : BHist}
    (carrier : AdjunctionUnitCounitCarrier p q a unit counit left right) :
    (hsame left BHist.Empty ∧ hsame right BHist.Empty) ↔
      hsame unit BHist.Empty ∧ hsame counit BHist.Empty := by
  constructor
  · intro roundtripEmpty
    have data :=
      EquivCatAdjunction_empty_roundtrip_prefix_determinacy carrier
        roundtripEmpty.left roundtripEmpty.right
    exact And.intro data.right.left data.right.right.left
  · intro unitCounitEmpty
    cases unitCounitEmpty.left
    cases unitCounitEmpty.right
    have leftEmpty : hsame left BHist.Empty :=
      cont_deterministic carrier.right.right.left (cont_right_unit BHist.Empty)
    have rightEmpty : hsame right BHist.Empty :=
      cont_deterministic carrier.right.right.right (cont_right_unit BHist.Empty)
    exact And.intro leftEmpty rightEmpty

theorem EquivCatAdjunction_empty_roundtrip_unit_counit_deterministic
    {p q a unit unit' counit counit' left right left' right' : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      AdjunctionUnitCounitCarrier p q a unit' counit' left' right' ->
        hsame left BHist.Empty -> hsame right BHist.Empty ->
          hsame left' BHist.Empty -> hsame right' BHist.Empty ->
            hsame unit unit' ∧ hsame counit counit' := by
  intro carrier carrier' leftEmpty rightEmpty leftEmpty' rightEmpty'
  have boundary :=
    EquivCatAdjunction_empty_roundtrip_prefix_determinacy carrier leftEmpty rightEmpty
  have boundary' :=
    EquivCatAdjunction_empty_roundtrip_prefix_determinacy carrier' leftEmpty' rightEmpty'
  exact And.intro
    (hsame_trans boundary.right.left (hsame_symm boundary'.right.left))
    (hsame_trans boundary.right.right.left (hsame_symm boundary'.right.right.left))

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

theorem EquivCatCycleIdentityCarrier_target_prefix_hsame_transport
    {p q q' a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      hsame left BHist.Empty ->
        hsame right BHist.Empty ->
          hsame q q' ->
            AdjunctionUnitCounitCarrier p q' a BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty ∧
              NatTransPrefixComponentCarrier p q' a BHist.Empty ∧
              NatTransPrefixComponentCarrier q' p a BHist.Empty := by
  intro carrier leftEmpty rightEmpty sameTarget
  have boundary :=
    EquivCatAdjunction_empty_roundtrip_prefix_determinacy carrier leftEmpty rightEmpty
  have unitData :=
    Iff.mp NatTransPrefixComponentCarrier_empty_identity_iff boundary.right.right.right.left
  have sameSourceTarget : hsame p q' :=
    hsame_trans boundary.left sameTarget
  have unitCarrier : NatTransPrefixComponentCarrier p q' a BHist.Empty :=
    Iff.mpr NatTransPrefixComponentCarrier_empty_identity_iff
      (And.intro unitData.left
        (And.intro
          (unary_transport unitData.right.left sameTarget)
          (And.intro unitData.right.right.left sameSourceTarget)))
  have counitCarrier : NatTransPrefixComponentCarrier q' p a BHist.Empty :=
    Iff.mpr NatTransPrefixComponentCarrier_empty_identity_iff
      (And.intro
        (unary_transport unitData.right.left sameTarget)
        (And.intro unitData.left
          (And.intro unitData.right.right.left (hsame_symm sameSourceTarget))))
  have transported :
      AdjunctionUnitCounitCarrier p q' a BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty :=
    Iff.mpr AdjunctionUnitCounitCarrier_empty_components_iff
      (And.intro unitData.left
        (And.intro
          (unary_transport unitData.right.left sameTarget)
          (And.intro unitData.right.right.left
            (And.intro sameSourceTarget
              (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))))))
  exact And.intro transported (And.intro unitCarrier counitCarrier)

theorem EquivCatAdjunction_empty_roundtrip_target_prefix_hsame_transport
    {p q q' a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty -> hsame q q' ->
        AdjunctionUnitCounitCarrier p q' a BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
          NatTransPrefixComponentCarrier p q' a BHist.Empty ∧
            NatTransPrefixComponentCarrier q' p a BHist.Empty := by
  intro carrier leftEmpty rightEmpty sameQQ'
  have boundary :=
    EquivCatAdjunction_empty_roundtrip_prefix_determinacy carrier leftEmpty rightEmpty
  have componentData :=
    (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mp
      boundary.right.right.right.left
  have q'Carrier : UnaryHistory q' :=
    unary_transport componentData.right.left sameQQ'
  have samePQ' : hsame p q' :=
    hsame_trans boundary.left sameQQ'
  have transported :
      AdjunctionUnitCounitCarrier p q' a BHist.Empty BHist.Empty BHist.Empty BHist.Empty :=
    (AdjunctionUnitCounitCarrier_empty_components_iff
      (p := p) (q := q') (a := a) (left := BHist.Empty) (right := BHist.Empty)).mpr
      ⟨componentData.left, q'Carrier, componentData.right.right.left, samePQ',
        hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩
  exact And.intro transported (And.intro transported.left transported.right.left)

theorem EquivCatAdjunction_empty_roundtrip_source_prefix_hsame_transport
    {p p' q a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      hsame left BHist.Empty -> hsame right BHist.Empty -> hsame p p' ->
        AdjunctionUnitCounitCarrier p' q a BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
          NatTransPrefixComponentCarrier p' q a BHist.Empty ∧
            NatTransPrefixComponentCarrier q p' a BHist.Empty := by
  intro carrier leftEmpty rightEmpty samePP'
  have boundary :=
    EquivCatAdjunction_empty_roundtrip_prefix_determinacy carrier leftEmpty rightEmpty
  have componentData :=
    (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mp
      boundary.right.right.right.left
  have p'Carrier : UnaryHistory p' :=
    unary_transport componentData.left samePP'
  have sameP'Q : hsame p' q :=
    hsame_trans (hsame_symm samePP') boundary.left
  have transported :
      AdjunctionUnitCounitCarrier p' q a BHist.Empty BHist.Empty BHist.Empty BHist.Empty :=
    (AdjunctionUnitCounitCarrier_empty_components_iff
      (p := p') (q := q) (a := a) (left := BHist.Empty) (right := BHist.Empty)).mpr
      ⟨p'Carrier, componentData.right.left, componentData.right.right.left, sameP'Q,
        hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩
  exact And.intro transported (And.intro transported.left transported.right.left)

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
