import BEDC.Derived.NatTransUp

namespace BEDC.Derived.YonedaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
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

theorem YonedaRepresentable_empty_component_family_displayed_deterministic {p q displayed : BHist} :
    (forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty) ->
      (forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a displayed) ->
        hsame BHist.Empty displayed := by
  intro emptyFamily displayedFamily
  have emptyComponent :
      NatTransPrefixComponentCarrier p q BHist.Empty BHist.Empty :=
    emptyFamily (a := BHist.Empty) unary_empty
  have displayedComponent :
      NatTransPrefixComponentCarrier p q BHist.Empty displayed :=
    displayedFamily (a := BHist.Empty) unary_empty
  exact
    CategoryHomCarrier_morphism_deterministic
      emptyComponent.right.right.right displayedComponent.right.right.right

end BEDC.Derived.YonedaUp
