import BEDC.FKernel.Unary.History
import BEDC.FKernel.Cont.Step

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem unary_cont_e0_result_absurd {h k z : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k (BHist.e0 z) -> False := by
  intro uh uk hcont
  exact unary_no_zero_extension (unary_cont_closed uh uk hcont)

theorem unary_cont_e1_result_cases {h k r : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k (BHist.e1 r) ->
      (k = BHist.Empty ∧ hsame h (BHist.e1 r)) ∨
        (∃ k0 : BHist, k = BHist.e1 k0 ∧ UnaryHistory k0 ∧ Cont h k0 r) := by
  intro _uh uk hcont
  have split := (cont_result_e1_cases_iff (h := h) (k := k) (r := r)).mp hcont
  cases split with
  | inl emptyCase =>
      exact Or.inl emptyCase
  | inr stepCase =>
      cases stepCase with
      | intro k0 data =>
          cases data with
          | intro kEq tail =>
              cases kEq
              exact Or.inr (Exists.intro k0 (And.intro rfl (And.intro uk tail)))

end BEDC.FKernel.Unary
