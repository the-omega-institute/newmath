import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist BEDC.FKernel.Cont

theorem CategoryHomCarrier_comp_endpoint_cycle_morphism_empty_iff {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (hsame a c <-> hsame fg BHist.Empty) := by
  intro left right comp
  constructor
  · exact CategoryHomCarrier_comp_endpoint_cycle_morphism_empty left right comp
  · intro sameMorphismEmpty
    have composite : CategoryHomCarrier a c fg := CategoryHomCarrier_comp_closed left right comp
    cases sameMorphismEmpty
    exact (CategoryHomCarrier_empty_identity_iff.mp composite).right.right

theorem ContinuationMorphism_comp_endpoint_cycle_boundary_iff {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame a c <-> hsame left.tail BHist.Empty ∧ hsame right.tail BHist.Empty ∧
      hsame a b ∧ hsame b c := by
  constructor
  · exact ContinuationMorphism_comp_endpoint_cycle_boundary left right
  · intro boundary
    exact hsame_trans boundary.right.right.left boundary.right.right.right

end BEDC.Derived.CategoryUp
