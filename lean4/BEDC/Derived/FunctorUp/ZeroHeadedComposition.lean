import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_zero_headed_component_absurd {p a b c f g fg : BHist} :
    CategoryHomCarrier (append p a) (append p b) f →
      CategoryHomCarrier (append p b) (append p c) g → Cont f g fg →
        ((∃ w : BHist, p = BHist.e0 w) ∨ (∃ w : BHist, a = BHist.e0 w) ∨
          (∃ w : BHist, b = BHist.e0 w) ∨ (∃ w : BHist, c = BHist.e0 w) ∨
            (∃ w : BHist, f = BHist.e0 w) ∨ (∃ w : BHist, g = BHist.e0 w) ∨
              (∃ w : BHist, fg = BHist.e0 w)) →
          False := by
  intro left right comp zeroComponent
  have composite : CategoryHomCarrier (append p a) (append p c) fg :=
    CategoryHomCarrier_comp_closed left right comp
  cases zeroComponent with
  | inl prefixZero =>
      exact FunctorPrefixHomCarrier_zero_headed_component_absurd left (Or.inl prefixZero)
  | inr rest =>
      cases rest with
      | inl sourceZero =>
          exact FunctorPrefixHomCarrier_zero_headed_component_absurd left
            (Or.inr (Or.inl sourceZero))
      | inr rest =>
          cases rest with
          | inl middleZero =>
              exact FunctorPrefixHomCarrier_zero_headed_component_absurd left
                (Or.inr (Or.inr (Or.inl middleZero)))
          | inr rest =>
              cases rest with
              | inl targetZero =>
                  exact FunctorPrefixHomCarrier_zero_headed_component_absurd right
                    (Or.inr (Or.inr (Or.inl targetZero)))
              | inr rest =>
                  cases rest with
                  | inl leftMorphismZero =>
                      exact FunctorPrefixHomCarrier_zero_headed_component_absurd left
                        (Or.inr (Or.inr (Or.inr leftMorphismZero)))
                  | inr rest =>
                      cases rest with
                      | inl rightMorphismZero =>
                          exact FunctorPrefixHomCarrier_zero_headed_component_absurd right
                            (Or.inr (Or.inr (Or.inr rightMorphismZero)))
                      | inr compositeMorphismZero =>
                          exact FunctorPrefixHomCarrier_zero_headed_component_absurd composite
                            (Or.inr (Or.inr (Or.inr compositeMorphismZero)))

end BEDC.Derived.FunctorUp
