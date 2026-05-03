import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_comp_target_visible {a b c f g fg : BHist} :
    CategoryHomCarrier (BHist.e1 a) b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      ∃ r : BHist, c = BHist.e1 r ∧ UnaryHistory r := by
  intro left right comp
  have composite : CategoryHomCarrier (BHist.e1 a) c fg :=
    CategoryHomCarrier_comp_closed left right comp
  cases CategoryHomCarrier_e1_source_morphism_cases composite with
  | inl emptyCase =>
      exact Exists.intro a (And.intro emptyCase.right.left emptyCase.right.right)
  | inr visibleCase =>
      cases visibleCase with
      | intro _k rest =>
          cases rest with
          | intro r data =>
              exact Exists.intro r
                (And.intro data.right.left data.right.right.right.right.left)

end BEDC.Derived.CategoryUp
