import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_empty_middle_inversion {p a c f g fg : BHist} :
    CategoryHomCarrier (append p a) BHist.Empty f ->
      CategoryHomCarrier BHist.Empty (append p c) g -> Cont f g fg ->
        hsame p BHist.Empty ∧ hsame a BHist.Empty ∧ hsame f BHist.Empty ∧
          hsame g (append p c) ∧ CategoryHomCarrier BHist.Empty (append p c) fg ∧
            hsame fg (append p c) := by
  intro left right comp
  have leftParts :=
    (FunctorPrefixHomCarrier_empty_target_components_iff (p := p) (a := a) (f := f)).mp
      left
  have rightParts :=
    (FunctorPrefixHomCarrier_empty_source_components_iff (p := p) (b := c) (f := g)).mp
      right
  have targetCarrier : BEDC.FKernel.Unary.UnaryHistory (append p c) := right.right.left
  have sameCompositeTarget : hsame fg (append p c) := by
    cases leftParts.right.right
    exact hsame_trans (cont_left_unit_result comp) rightParts.right.right
  exact And.intro leftParts.left
    (And.intro leftParts.right.left
      (And.intro leftParts.right.right
        (And.intro rightParts.right.right
          (And.intro
            ((CategoryHomCarrier_empty_source_iff (b := append p c) (f := fg)).mpr
              (And.intro targetCarrier sameCompositeTarget))
            sameCompositeTarget))))

theorem FunctorPrefixHomCarrier_comp_empty_middle_target_deterministic
    {p a c f g fg target : BHist} :
    CategoryHomCarrier (append p a) BHist.Empty f ->
      CategoryHomCarrier BHist.Empty (append p c) g -> Cont f g fg ->
        CategoryHomCarrier BHist.Empty target fg -> hsame target (append p c) := by
  intro left right comp displayed
  have inverted :=
    FunctorPrefixHomCarrier_comp_empty_middle_inversion
      (p := p) (a := a) (c := c) (f := f) (g := g) (fg := fg) left right comp
  exact hsame_symm (CategoryHomCarrier_target_deterministic inverted.right.right.right.right.left
    displayed)

theorem FunctorPrefixHomCarrier_e1_endpoint_empty_composite_middle_hsame
    {p a b c f g : BHist} :
    CategoryHomCarrier (append p (BHist.e1 a)) b f ->
      CategoryHomCarrier b (append p (BHist.e1 c)) g ->
        Cont f g BHist.Empty ->
          hsame b (append p (BHist.e1 a)) ∧ hsame b (append p (BHist.e1 c)) := by
  intro left right comp
  have emptyData :=
    (FunctorPrefixHomCarrier_e1_endpoint_empty_composite_iff (p := p) (a := a)
      (b := b) (c := c) (f := f) (g := g) left right).mp comp
  have leftEmpty : CategoryHomCarrier (append p (BHist.e1 a)) b BHist.Empty :=
    CategoryHomCarrier_hsame_transport (hsame_refl (append p (BHist.e1 a)))
      (hsame_refl b) emptyData.left left
  have rightEmpty : CategoryHomCarrier b (append p (BHist.e1 c)) BHist.Empty :=
    CategoryHomCarrier_hsame_transport (hsame_refl b)
      (hsame_refl (append p (BHist.e1 c))) emptyData.right.left right
  exact And.intro
    (hsame_symm (CategoryHomCarrier_empty_identity_iff.mp leftEmpty).right.right)
    (CategoryHomCarrier_empty_identity_iff.mp rightEmpty).right.right

end BEDC.Derived.FunctorUp
