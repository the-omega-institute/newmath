import BEDC.Derived.NatTransUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.YonedaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
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

theorem YonedaRepresentable_empty_component_family_semanticNameCert {p : BHist}
    (prefixCarrier : UnaryHistory p) :
    SemanticNameCert
      (fun q : BHist => forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty)
      (fun q : BHist => forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty)
      (fun q : BHist => forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty)
      hsame := by
  constructor
  · constructor
    · exact Exists.intro p
        (by
          intro a objectCarrier
          exact
            (NatTransPrefixComponentCarrier_empty_identity_iff
              (p := p) (q := p) (a := a)).mpr
              (And.intro prefixCarrier
                (And.intro prefixCarrier
                  (And.intro objectCarrier (hsame_refl p)))))
    · intro q _familyCarrier
      exact hsame_refl q
    · intro q r sameQR
      exact hsame_symm sameQR
    · intro q r s sameQR sameRS
      exact hsame_trans sameQR sameRS
    · intro q r sameQR familyCarrier
      intro a objectCarrier
      cases sameQR
      exact familyCarrier objectCarrier
  · intro q source
    exact source
  · intro q source
    exact source

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

theorem YonedaRepresentable_empty_component_family_boundary_hsame_iff {p q r s : BHist} :
    (forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty) ->
      (forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier r s a BHist.Empty) ->
        (hsame p r ↔ hsame q s) := by
  intro leftFamily rightFamily
  have leftData := YonedaRepresentable_empty_component_family_iff.mp leftFamily
  have rightData := YonedaRepresentable_empty_component_family_iff.mp rightFamily
  constructor
  · intro samePR
    exact hsame_trans (hsame_symm leftData.right.right)
      (hsame_trans samePR rightData.right.right)
  · intro sameQS
    exact hsame_trans leftData.right.right
      (hsame_trans sameQS (hsame_symm rightData.right.right))

end BEDC.Derived.YonedaUp
