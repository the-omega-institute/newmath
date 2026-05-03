import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_morphism_empty_endpoint_iff {a b f : BHist} :
    CategoryHomCarrier a b f -> (hsame f BHist.Empty ↔ hsame a b) := by
  intro homCarrier
  constructor
  · intro morphEmpty
    cases morphEmpty
    exact hsame_symm (cont_deterministic homCarrier.right.right.right (cont_right_unit a))
  · intro endpointSame
    apply append_left_cancel (h := a)
    exact homCarrier.right.right.right.symm.trans endpointSame.symm

end BEDC.Derived.CategoryUp
