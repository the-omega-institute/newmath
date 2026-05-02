import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_e1_target_empty_morphism_iff {a r : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) BHist.Empty ↔
      UnaryHistory a ∧ hsame a r := by
  constructor
  · intro homCarrier
    have cases := CategoryHomCarrier_left_e1_result_cases homCarrier
    cases cases with
    | inl emptyCase =>
        exact emptyCase.right
    | inr visibleCase =>
        cases visibleCase with
        | intro k0 data =>
            cases data with
            | intro emptyEq _rest =>
                cases emptyEq
  · intro data
    exact
      CategoryHomCarrier_empty_identity_iff.mpr
        (And.intro (unary_e1_closed data.left)
          (And.intro (unary_e1_closed (unary_transport data.left data.right))
            (hsame_e1_congr data.right)))

end BEDC.Derived.CategoryUp
