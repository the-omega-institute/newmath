import BEDC.Derived.FunctorUp
import BEDC.Derived.CategoryUp.MorphismEmptyEndpoint

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_morphism_empty_endpoint_iff {p a b f : BHist} :
    CategoryHomCarrier (append p a) (append p b) f -> (hsame f BHist.Empty <-> hsame a b) := by
  intro homCarrier
  constructor
  · intro morphismEmpty
    have sameEndpoints :
        hsame (append p a) (append p b) :=
      (CategoryHomCarrier_morphism_empty_endpoint_iff homCarrier).mp morphismEmpty
    exact append_left_cancel (h := p) sameEndpoints
  · intro sameEndpoints
    have samePrefixed : hsame (append p a) (append p b) := by
      cases sameEndpoints
      rfl
    exact (CategoryHomCarrier_morphism_empty_endpoint_iff homCarrier).mpr samePrefixed

end BEDC.Derived.FunctorUp
