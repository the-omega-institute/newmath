import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_nonempty_target_component_split {p a b c f g fg : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g fg ->
        (hsame fg BHist.Empty -> False) ->
          (hsame p BHist.Empty -> False) ∨ (hsame c BHist.Empty -> False) := by
  intro left right comp compositeNonempty
  have targetNonempty : hsame (append p c) BHist.Empty -> False :=
    CategoryHomCarrier_comp_morphism_nonempty_target_not_empty left right comp compositeNonempty
  exact append_nonempty_iff.mp targetNonempty

end BEDC.Derived.FunctorUp
