import BEDC.Derived.NatTransUp

namespace BEDC.Derived.YonedaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatTransUp

theorem YonedaRepresentable_empty_component_family_iff {p q : BHist} :
    ((forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty) <->
      UnaryHistory p /\ UnaryHistory q /\ hsame p q) := by
  constructor
  · intro familyCarrier
    have emptyComponent :
        NatTransPrefixComponentCarrier p q BHist.Empty BHist.Empty :=
      familyCarrier (a := BHist.Empty) unary_empty
    have data :=
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := p) (q := q) (a := BHist.Empty)).mp emptyComponent
    exact And.intro data.left (And.intro data.right.left data.right.right.right)
  · intro data
    intro a objectCarrier
    exact
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := p) (q := q) (a := a)).mpr
        (And.intro data.left
          (And.intro data.right.left
            (And.intro objectCarrier data.right.right)))

theorem YonedaRepresentable_empty_component_family_target_deterministic {p q r : BHist} :
    (forall {a : BHist}, UnaryHistory a ->
      NatTransPrefixComponentCarrier p q a BHist.Empty) ->
    (forall {a : BHist}, UnaryHistory a ->
      NatTransPrefixComponentCarrier p r a BHist.Empty) ->
    hsame q r := by
  intro leftFamily rightFamily
  have leftData := YonedaRepresentable_empty_component_family_iff.mp leftFamily
  have rightData := YonedaRepresentable_empty_component_family_iff.mp rightFamily
  exact hsame_trans (hsame_symm leftData.right.right) rightData.right.right

end BEDC.Derived.YonedaUp
