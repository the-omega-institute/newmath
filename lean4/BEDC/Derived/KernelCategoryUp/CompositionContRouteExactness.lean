import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_composition_cont_route_exactness
    {object hom identity composition associativity unit provenance name a b c f g fg routeRead :
      BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      CategoryHomCarrier a b f →
        CategoryHomCarrier b c g →
          Cont f g fg →
            UnaryHistory name →
              Cont fg name routeRead →
                CategoryHomCarrier a c fg ∧ UnaryHistory routeRead ∧ Cont f g fg ∧
                  Cont fg name routeRead ∧ hsame associativity (append hom composition) ∧
                    hsame unit identity ∧ hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CategoryHomCarrier
  intro carrier left right comp nameUnary fgNameRoute
  have composite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  have fgUnary : UnaryHistory fg := composite.right.right.left
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed fgUnary nameUnary fgNameRoute
  exact
    ⟨composite, routeReadUnary, comp, fgNameRoute, carrier.right.right.right.left,
      carrier.right.right.right.right.left, carrier.right.right.right.right.right⟩

end BEDC.Derived.KernelCategoryUp
