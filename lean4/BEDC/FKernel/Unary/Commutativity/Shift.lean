import BEDC.FKernel.Unary.Commutativity

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem unary_shift_witness_closed_result_pair {k h r' : BHist} :
    UnaryHistory k -> UnaryHistory h -> Cont k (BHist.e1 h) r' ->
      exists v : BHist, Cont k h v ∧ hsame r' (BHist.e1 v) ∧
        UnaryHistory v ∧ UnaryHistory r' := by
  intro uk uh hr
  cases unary_shift_witness uk hr with
  | intro v shifted =>
      cases shifted with
      | intro hv same =>
          have uv : UnaryHistory v := unary_cont_closed uk uh hv
          have ur : UnaryHistory r' := unary_transport (unary_e1_closed uv) (hsame_symm same)
          exact ⟨v, hv, same, uv, ur⟩

theorem unary_shift_witness_by_induction {k h r : BHist} :
    UnaryHistory k -> Cont k (BHist.e1 h) r ->
      exists v : BHist, Cont k h v /\ hsame r (BHist.e1 v) := by
  intro uk hr
  induction k generalizing h r with
  | Empty =>
      exact unary_shift_base hr
  | e0 _ _ =>
      cases uk
  | e1 k ih =>
      exact unary_shift_step uk (by
        intro r hshift
        exact ih uk hshift) hr

end BEDC.FKernel.Unary
