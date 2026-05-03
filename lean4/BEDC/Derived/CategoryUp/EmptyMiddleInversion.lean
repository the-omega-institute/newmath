import BEDC.Derived.CategoryUp.EmptySourceComposite

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

end BEDC.Derived.CategoryUp
