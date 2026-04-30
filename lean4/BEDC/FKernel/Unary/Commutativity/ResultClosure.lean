import BEDC.FKernel.Unary.Commutativity

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem unary_commutativity_refined_with_result_closure {h k r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r' ->
      hsame r r' /\ UnaryHistory r /\ UnaryHistory r' := by
  intro uh uk hr hr'
  constructor
  · exact unary_commutativity_refined uh uk hr hr'
  · constructor
    · exact unary_cont_closed uh uk hr
    · exact unary_cont_closed uk uh hr'

theorem unary_shift_step_with_unique_witness {k0 h r' : BHist} :
    UnaryHistory k0 →
      (∀ {r : BHist}, Cont k0 (.e1 h) r →
        ∃ v : BHist, Cont k0 h v ∧ hsame r (.e1 v)) →
      Cont (.e1 k0) (.e1 h) r' →
      ∃ v : BHist,
        Cont (.e1 k0) h v ∧ hsame r' (.e1 v) ∧
          (∀ {w : BHist}, Cont (.e1 k0) h w → hsame v w) := by
  intro uk shift hr'
  cases unary_shift_step uk shift hr' with
  | intro v shifted =>
      cases shifted with
      | intro hv same =>
          exact ⟨v, hv, same, by
            intro w hw
            exact cont_deterministic hv hw⟩

theorem unary_shift_step_closed_unique_witness {k0 h r' : BHist} :
    UnaryHistory k0 → UnaryHistory h →
      (∀ {r : BHist}, Cont k0 (BHist.e1 h) r →
        ∃ v : BHist, Cont k0 h v ∧ hsame r (BHist.e1 v)) →
      Cont (BHist.e1 k0) (BHist.e1 h) r' →
      ∃ v : BHist,
        Cont (BHist.e1 k0) h v ∧ hsame r' (BHist.e1 v) ∧
          UnaryHistory v ∧ UnaryHistory r' ∧
            (∀ {w : BHist}, Cont (BHist.e1 k0) h w → hsame v w) := by
  intro uk uh shift hr'
  cases unary_shift_step uk shift hr' with
  | intro v shifted =>
      cases shifted with
      | intro hv same =>
          have uv : UnaryHistory v := unary_cont_closed (unary_e1_closed uk) uh hv
          have ur' : UnaryHistory r' := unary_transport (unary_e1_closed uv) (hsame_symm same)
          exact ⟨v, hv, same, uv, ur', by
            intro w hw
            exact cont_deterministic hv hw⟩

end BEDC.FKernel.Unary
