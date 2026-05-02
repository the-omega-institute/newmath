import BEDC.Derived.CategoryUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CategoryHomCarrier_cycle_tails_empty {a b f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b a g ->
      hsame a b ∧ hsame f BHist.Empty ∧ hsame g BHist.Empty := by
  intro left right
  have sameEndpoint : hsame a b :=
    cont_mutual_extension_hsame left.right.right.right right.right.right.right
  have tailsEmpty : hsame f BHist.Empty ∧ hsame g BHist.Empty :=
    cont_mutual_extension_tails_empty left.right.right.right right.right.right.right
  exact And.intro sameEndpoint tailsEmpty

theorem ContinuationMorphism_cycle_tails_empty {a b : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b a) :
    hsame a b ∧ hsame left.tail BHist.Empty ∧ hsame right.tail BHist.Empty := by
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          exact And.intro
            (cont_mutual_extension_hsame leftRel rightRel)
            (cont_mutual_extension_tails_empty leftRel rightRel)

theorem CategoryHomCarrier_e1_morphism_cycle_absurd {a b k g : BHist} :
    CategoryHomCarrier a b (BHist.e1 k) -> CategoryHomCarrier b a g -> False := by
  intro left right
  have cycle := CategoryHomCarrier_cycle_tails_empty left right
  exact not_hsame_e1_empty cycle.right.left

theorem CategoryHomCarrier_cycle_identity_carriers {a b f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b a g ->
      CategoryHomCarrier a a BHist.Empty ∧ CategoryHomCarrier b b BHist.Empty ∧ hsame a b := by
  intro left right
  have cycle := CategoryHomCarrier_cycle_tails_empty left right
  have sameEndpoint : hsame a b := cycle.left
  have fEmpty : hsame f BHist.Empty := cycle.right.left
  have gEmpty : hsame g BHist.Empty := cycle.right.right
  constructor
  · exact CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_symm sameEndpoint)
      fEmpty left
  · constructor
    · exact CategoryHomCarrier_hsame_transport (hsame_refl b) sameEndpoint gEmpty right
    · exact sameEndpoint

theorem CategoryHomCarrier_unary_suffix_cycle_tails_empty {q a b f g : BHist} :
    CategoryHomCarrier (append a q) (append b q) f -> CategoryHomCarrier b a g ->
      hsame a b ∧ hsame f BHist.Empty ∧ hsame g BHist.Empty := by
  intro left right
  have baseLeft : CategoryHomCarrier a b f :=
    (CategoryHomCarrier_unary_suffix_iff.mp left).right
  exact CategoryHomCarrier_cycle_tails_empty baseLeft right

theorem CategoryHomCarrier_unary_suffix_cycle_identity_carriers {q a b f g : BHist} :
    CategoryHomCarrier (append a q) (append b q) f -> CategoryHomCarrier b a g ->
      CategoryHomCarrier a a BHist.Empty ∧ CategoryHomCarrier b b BHist.Empty ∧ hsame a b := by
  intro left right
  have baseLeft : CategoryHomCarrier a b f :=
    (CategoryHomCarrier_unary_suffix_iff.mp left).right
  exact CategoryHomCarrier_cycle_identity_carriers baseLeft right

end BEDC.Derived.CategoryUp
