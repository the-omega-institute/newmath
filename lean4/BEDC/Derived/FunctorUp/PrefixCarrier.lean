import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

structure PrefixFunctorCarrier (p : BHist) : Prop where
  prefix_unary : UnaryHistory p
  hom_preserves : forall {a b f : BHist},
    CategoryHomCarrier a b f -> CategoryHomCarrier (append p a) (append p b) f
  hom_reflects : forall {a b f : BHist},
    CategoryHomCarrier (append p a) (append p b) f -> CategoryHomCarrier a b f
  comp_preserves : forall {a b c f g fg : BHist},
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg

protected theorem PrefixFunctorCarrier_from_unary_prefix {p : BHist} :
    UnaryHistory p -> PrefixFunctorCarrier p := by
  intro prefixCarrier
  constructor
  · exact prefixCarrier
  · intro _a _b _f homCarrier
    exact FunctorPrefixHomCarrier_preserves prefixCarrier homCarrier
  · intro _a _b _f prefixedCarrier
    exact FunctorPrefixHomCarrier_reflects prefixedCarrier
  · intro _a _b _c _f _g _fg left right comp
    exact FunctorPrefixHomCarrier_comp_preserves prefixCarrier left right comp

theorem PrefixFunctorCarrier_hsame_transport_with_unary {p q : BHist} :
    PrefixFunctorCarrier p -> hsame p q -> PrefixFunctorCarrier q ∧ UnaryHistory q := by
  intro prefixCarrier samePrefix
  cases samePrefix
  exact And.intro prefixCarrier prefixCarrier.prefix_unary

theorem PrefixFunctorCarrier_comp_public_readback {p a b c f g fg : BHist} :
    PrefixFunctorCarrier p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      Cont f g fg ->
        CategoryHomCarrier (append p a) (append p c) fg ∧
          (∀ {displayed : BHist},
            CategoryHomCarrier (append p a) (append p c) displayed -> hsame fg displayed) := by
  intro prefixCarrier left right comp
  have compositeCarrier : CategoryHomCarrier (append p a) (append p c) fg :=
    prefixCarrier.comp_preserves left right comp
  exact
    And.intro compositeCarrier
      (fun displayedCarrier =>
        CategoryHomCarrier_morphism_deterministic compositeCarrier displayedCarrier)

theorem PrefixFunctorCarrier_hom_public_readback {p a b f : BHist} :
    PrefixFunctorCarrier p ->
      CategoryHomCarrier a b f ->
        CategoryHomCarrier (append p a) (append p b) f ∧
          (∀ {displayed : BHist},
            CategoryHomCarrier (append p a) (append p b) displayed -> hsame f displayed) := by
  intro prefixCarrier homCarrier
  have displayedCarrier : CategoryHomCarrier (append p a) (append p b) f :=
    prefixCarrier.hom_preserves homCarrier
  exact And.intro displayedCarrier
    (fun displayed => CategoryHomCarrier_morphism_deterministic displayedCarrier displayed)

theorem PrefixFunctorCarrier_append_hom_preserves {p q a b f : BHist} :
    PrefixFunctorCarrier p -> PrefixFunctorCarrier q -> CategoryHomCarrier a b f ->
      CategoryHomCarrier (append (append p q) a) (append (append p q) b) f := by
  intro prefixP prefixQ homCarrier
  have qClosed : CategoryHomCarrier (append q a) (append q b) f :=
    prefixQ.hom_preserves homCarrier
  have pClosed : CategoryHomCarrier (append p (append q a)) (append p (append q b)) f :=
    prefixP.hom_preserves qClosed
  exact
    CategoryHomCarrier_hsame_transport
      (append_assoc p q a).symm
      (append_assoc p q b).symm
      (hsame_refl f)
      pClosed

theorem PrefixFunctorCarrier_append_comp_preserves {p q a b c f g fg : BHist} :
    PrefixFunctorCarrier p -> PrefixFunctorCarrier q -> CategoryHomCarrier a b f ->
      CategoryHomCarrier b c g -> Cont f g fg ->
        CategoryHomCarrier (append (append p q) a) (append (append p q) c) fg := by
  intro prefixP prefixQ left right comp
  have qClosed : CategoryHomCarrier (append q a) (append q c) fg :=
    prefixQ.comp_preserves left right comp
  have pClosed : CategoryHomCarrier (append p (append q a)) (append p (append q c)) fg :=
    prefixP.hom_preserves qClosed
  exact
    CategoryHomCarrier_hsame_transport
      (append_assoc p q a).symm
      (append_assoc p q c).symm
      (hsame_refl fg)
      pClosed

theorem PrefixFunctorCarrier_e1_prefix_hom_reflects {p a b f : BHist} :
    PrefixFunctorCarrier (BHist.e1 p) ->
      CategoryHomCarrier (append (BHist.e1 p) a) (append (BHist.e1 p) b) f ->
        UnaryHistory p ∧ CategoryHomCarrier a b f := by
  intro prefixCarrier displayedCarrier
  exact And.intro (unary_e1_inversion prefixCarrier.prefix_unary)
    (prefixCarrier.hom_reflects displayedCarrier)

theorem PrefixFunctorCarrier_comp_assoc_public_readback
    {p a b c d f g h fg gh left right : BHist} :
    PrefixFunctorCarrier p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      CategoryHomCarrier c d h -> Cont f g fg -> Cont g h gh -> Cont fg h left ->
        Cont f gh right ->
          CategoryHomCarrier (append p a) (append p d) left ∧
            CategoryHomCarrier (append p a) (append p d) right ∧ hsame left right ∧
              (∀ {displayed : BHist},
                CategoryHomCarrier (append p a) (append p d) displayed ->
                  hsame left displayed ∧ hsame right displayed) := by
  intro prefixCarrier first second third fgRel ghRel leftRel rightRel
  have closed :=
    FunctorPrefixHomCarrier_comp_assoc_preserves
      prefixCarrier.prefix_unary first second third fgRel ghRel leftRel rightRel
  exact
    And.intro closed.left
      (And.intro closed.right.left
        (And.intro closed.right.right
          (fun displayedCarrier =>
            And.intro
              (CategoryHomCarrier_morphism_deterministic closed.left displayedCarrier)
              (CategoryHomCarrier_morphism_deterministic closed.right.left displayedCarrier))))

theorem PrefixFunctorCarrier_identity_public_readback {p a displayed : BHist} :
    PrefixFunctorCarrier p -> UnaryHistory a ->
      CategoryHomCarrier (append p a) (append p a) displayed -> hsame displayed BHist.Empty := by
  intro prefixCarrier sourceCarrier displayedCarrier
  have identityCarrier :
      CategoryHomCarrier (append p a) (append p a) BHist.Empty :=
    FunctorPrefixHomCarrier_identity_closed prefixCarrier.prefix_unary sourceCarrier
      (cont_right_unit BHist.Empty)
  exact CategoryHomCarrier_morphism_deterministic displayedCarrier identityCarrier

theorem PrefixFunctorCarrier_comp_right_factor_endpoint_deterministic {p a b b' c f g g' fg : BHist} :
    PrefixFunctorCarrier p -> CategoryHomCarrier a b f -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg -> Cont f g' fg ->
        CategoryHomCarrier b' c g' -> hsame b b' /\ hsame g g' := by
  intro prefixCarrier left comp displayed comp' right'
  have reflected : CategoryHomCarrier a c fg := prefixCarrier.hom_reflects displayed
  have sameEndpoint : hsame b b' :=
    CategoryHomCarrier_comp_middle_object_deterministic left right' comp' reflected
  have sameTail : hsame g g' := cont_left_cancel comp comp'
  exact And.intro sameEndpoint sameTail

theorem PrefixFunctorCarrier_append_assoc_comp_public_readback
    {p q r a b c f g fg leftDisplayed rightDisplayed : BHist} :
    PrefixFunctorCarrier p -> PrefixFunctorCarrier q -> PrefixFunctorCarrier r ->
      CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
        CategoryHomCarrier (append (append (append p q) r) a)
          (append (append (append p q) r) c) leftDisplayed ->
          CategoryHomCarrier (append (append p (append q r)) a)
            (append (append p (append q r)) c) rightDisplayed ->
            hsame leftDisplayed rightDisplayed := by
  intro prefixP prefixQ prefixR left right comp leftCarrier rightCarrier
  have prefixPQ : PrefixFunctorCarrier (append p q) :=
    BEDC.Derived.FunctorUp.PrefixFunctorCarrier_from_unary_prefix
      (unary_append_closed prefixP.prefix_unary prefixQ.prefix_unary)
  have prefixQR : PrefixFunctorCarrier (append q r) :=
    BEDC.Derived.FunctorUp.PrefixFunctorCarrier_from_unary_prefix
      (unary_append_closed prefixQ.prefix_unary prefixR.prefix_unary)
  have leftComposite :
      CategoryHomCarrier (append (append (append p q) r) a)
        (append (append (append p q) r) c) fg :=
    PrefixFunctorCarrier_append_comp_preserves prefixPQ prefixR left right comp
  have rightComposite :
      CategoryHomCarrier (append (append p (append q r)) a)
        (append (append p (append q r)) c) fg :=
    PrefixFunctorCarrier_append_comp_preserves prefixP prefixQR left right comp
  have sameLeft : hsame fg leftDisplayed :=
    CategoryHomCarrier_morphism_deterministic leftComposite leftCarrier
  have sameRight : hsame fg rightDisplayed :=
    CategoryHomCarrier_morphism_deterministic rightComposite rightCarrier
  exact hsame_trans (hsame_symm sameLeft) sameRight

end BEDC.Derived.FunctorUp
