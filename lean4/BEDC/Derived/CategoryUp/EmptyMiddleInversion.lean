import BEDC.Derived.CategoryUp.EmptySourceComposite
import BEDC.Derived.CategoryUp.EmptyComposite

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_comp_empty_middle_inversion {a c f g fg : BHist} :
    CategoryHomCarrier a BHist.Empty f -> CategoryHomCarrier BHist.Empty c g -> Cont f g fg ->
      hsame a BHist.Empty ∧ hsame f BHist.Empty ∧ hsame g c ∧
        CategoryHomCarrier BHist.Empty c fg ∧ hsame fg c := by
  intro left right comp
  have leftEmpty := Iff.mp CategoryHomCarrier_empty_target_iff left
  have rightReadback := Iff.mp CategoryHomCarrier_empty_source_iff right
  have composite : CategoryHomCarrier a c fg := CategoryHomCarrier_comp_closed left right comp
  have compositeEmptySource : CategoryHomCarrier BHist.Empty c fg :=
    CategoryHomCarrier_hsame_transport leftEmpty.left (hsame_refl c) (hsame_refl fg)
      composite
  have compositeReadback := Iff.mp CategoryHomCarrier_empty_source_iff compositeEmptySource
  exact ⟨leftEmpty.left, leftEmpty.right, rightReadback.right, compositeEmptySource,
    compositeReadback.right⟩

theorem CategoryHomCarrier_comp_empty_middle_displayed_morphism_deterministic
    {a c f g fg displayed : BHist} :
    CategoryHomCarrier a BHist.Empty f -> CategoryHomCarrier BHist.Empty c g -> Cont f g fg ->
      CategoryHomCarrier BHist.Empty c displayed -> hsame displayed fg := by
  intro left right comp displayedCarrier
  have inverted :=
    CategoryHomCarrier_comp_empty_middle_inversion
      (a := a) (c := c) (f := f) (g := g) (fg := fg) left right comp
  exact CategoryHomCarrier_morphism_deterministic displayedCarrier inverted.right.right.right.left

theorem CategoryHomCarrier_comp_empty_middle_empty_result_components {a c f g fg : BHist} :
    CategoryHomCarrier a BHist.Empty f -> CategoryHomCarrier BHist.Empty c g -> Cont f g fg ->
      hsame fg BHist.Empty ->
        hsame a BHist.Empty ∧ hsame c BHist.Empty ∧ hsame f BHist.Empty ∧
          hsame g BHist.Empty := by
  intro left right comp resultEmpty
  have emptyData := (CategoryHomCarrier_comp_result_empty_iff left right comp).mp resultEmpty
  exact And.intro emptyData.right.right.left
    (And.intro (hsame_symm emptyData.right.right.right)
      (And.intro emptyData.left emptyData.right.left))

end BEDC.Derived.CategoryUp
