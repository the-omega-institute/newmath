import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem TrialDiv_unit_step_result_not_unit {b n b' : BHist} :
    TrialDiv b n ->
      Cont b (BHist.e1 BHist.Empty) b' ->
        hsame b' (BHist.e1 BHist.Empty) -> False := by
  intro trial step resultUnit
  have displayed : Cont b (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    cont_result_hsame_transport step resultUnit
  have emptyBound : hsame b BHist.Empty :=
    cont_right_cancel displayed (cont_left_unit (BHist.e1 BHist.Empty))
  exact TrialDiv_bound_not_empty trial emptyBound

theorem TrialDiv_unit_step_result_successor_shape {b n b' : BHist} :
    TrialDiv b n -> Cont b (BHist.e1 BHist.Empty) b' ->
      ∃ tail : BHist, hsame b' (BHist.e1 (BHist.e1 tail)) ∧ UnaryHistory tail := by
  intro trial step
  have resultUnary : UnaryHistory b' :=
    unary_cont_closed (TrialDiv_bound_unary trial) (unary_e1_closed unary_empty) step
  cases b' with
  | Empty =>
      have emptyParts := cont_empty_result_inversion step
      exact False.elim (not_hsame_e1_empty emptyParts.right)
  | e0 tail =>
      cases resultUnary
  | e1 tail =>
      cases tail with
      | Empty =>
          exact False.elim
            (TrialDiv_unit_step_result_not_unit trial step
              (hsame_refl (BHist.e1 BHist.Empty)))
      | e0 tail =>
          cases unary_e1_inversion resultUnary
      | e1 tail =>
          exact ⟨tail, hsame_refl (BHist.e1 (BHist.e1 tail)),
            unary_e1_inversion (unary_e1_inversion resultUnary)⟩

end BEDC.Derived.PrimeUp
