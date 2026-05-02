import BEDC.Derived.CategoryUp
import BEDC.Derived.CategoryUp.Prefix
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

theorem ContinuationMorphism_triangle_cycle_tails_empty {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c)
    (back : ContinuationMorphism c a) :
    hsame left.tail BHist.Empty ∧ hsame right.tail BHist.Empty ∧
      hsame back.tail BHist.Empty ∧ hsame a b ∧ hsame b c := by
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases back with
          | mk backTail backRel =>
              have compositeRel : Cont a (append leftTail rightTail) c := by
                cases leftRel
                exact rightRel.trans (append_assoc a leftTail rightTail)
              have cycleTails :
                  hsame (append leftTail rightTail) BHist.Empty ∧
                    hsame backTail BHist.Empty :=
                cont_mutual_extension_tails_empty compositeRel backRel
              have emptyParts : leftTail = BHist.Empty ∧ rightTail = BHist.Empty :=
                append_eq_empty_iff.mp cycleTails.left
              cases emptyParts.left
              cases emptyParts.right
              exact
                And.intro (hsame_refl BHist.Empty)
                  (And.intro (hsame_refl BHist.Empty)
                    (And.intro cycleTails.right
                      (And.intro
                        (cont_deterministic (cont_right_unit a) leftRel)
                        (cont_deterministic (cont_right_unit b) rightRel))))

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

theorem CategoryHomCarrier_triangle_cycle_tails_empty {a b c f g h : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> CategoryHomCarrier c a h ->
      hsame f BHist.Empty ∧ hsame g BHist.Empty ∧ hsame h BHist.Empty ∧
        hsame a b ∧ hsame b c := by
  intro left right back
  have compositeRel : Cont a (append f g) c := by
    cases left.right.right.right
    exact right.right.right.right.trans (append_assoc a f g)
  have cycleTails :
      hsame (append f g) BHist.Empty ∧ hsame h BHist.Empty :=
    cont_mutual_extension_tails_empty compositeRel back.right.right.right
  have emptyParts : f = BHist.Empty ∧ g = BHist.Empty :=
    append_eq_empty_iff.mp cycleTails.left
  cases emptyParts.left
  cases emptyParts.right
  exact
    And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty)
        (And.intro cycleTails.right
          (And.intro
            (cont_deterministic (cont_right_unit a) left.right.right.right)
            (cont_deterministic (cont_right_unit b) right.right.right.right))))

theorem CategoryHomCarrier_triangle_cycle_identity_carriers {a b c f g h : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> CategoryHomCarrier c a h ->
      CategoryHomCarrier a a BHist.Empty ∧ CategoryHomCarrier b b BHist.Empty ∧
        CategoryHomCarrier c c BHist.Empty ∧ hsame a b ∧ hsame b c := by
  intro left right back
  have cycle := CategoryHomCarrier_triangle_cycle_tails_empty left right back
  have sameAC : hsame a c := hsame_trans cycle.right.right.right.left cycle.right.right.right.right
  exact
    And.intro
      (CategoryHomCarrier_hsame_transport (hsame_refl a)
        (hsame_symm cycle.right.right.right.left) cycle.left left)
      (And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl b)
          (hsame_symm cycle.right.right.right.right) cycle.right.left right)
        (And.intro
          (CategoryHomCarrier_hsame_transport (hsame_refl c) sameAC cycle.right.right.left back)
          (And.intro cycle.right.right.right.left cycle.right.right.right.right)))

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

theorem CategoryHomCarrier_unary_context_cycle_identity_carriers {p q a b f g : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append b q) (append a q) g ->
        CategoryHomCarrier a a BHist.Empty ∧ CategoryHomCarrier b b BHist.Empty ∧
          hsame a b := by
  intro left right
  have baseLeft : CategoryHomCarrier a b f :=
    (CategoryHomCarrier_unary_prefix_iff.mp left).right
  have baseRight : CategoryHomCarrier b a g :=
    (CategoryHomCarrier_unary_suffix_iff.mp right).right
  exact CategoryHomCarrier_cycle_identity_carriers baseLeft baseRight

end BEDC.Derived.CategoryUp
