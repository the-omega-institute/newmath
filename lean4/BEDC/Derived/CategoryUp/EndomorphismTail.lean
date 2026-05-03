import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_endomorphism_tail_empty_iff {a f : BHist} :
    CategoryHomCarrier a a f ↔ UnaryHistory a ∧ UnaryHistory f ∧ hsame f BHist.Empty := by
  constructor
  · intro homCarrier
    exact And.intro homCarrier.left
      (And.intro homCarrier.right.right.left
        (cont_right_unit_unique homCarrier.right.right.right))
  · intro data
    cases data with
    | intro sourceCarrier rest =>
        cases rest with
        | intro morphCarrier tailEmpty =>
            cases tailEmpty
            exact CategoryHomCarrier_empty_identity sourceCarrier

end BEDC.Derived.CategoryUp
