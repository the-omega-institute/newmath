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

end BEDC.Derived.FunctorUp
