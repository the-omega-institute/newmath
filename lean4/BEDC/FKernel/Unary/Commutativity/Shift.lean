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

theorem unary_shift_witness_closed_symmetric_result_pair {k h r' : BHist} :
    UnaryHistory k -> UnaryHistory h -> Cont k (BHist.e1 h) r' ->
      exists v : BHist, Cont k h v ∧ hsame r' (BHist.e1 v) ∧
        hsame (BHist.e1 v) r' ∧ UnaryHistory v ∧ UnaryHistory r' := by
  intro uk uh hr
  cases unary_shift_witness uk hr with
  | intro v shifted =>
      cases shifted with
      | intro hv same =>
          have uv : UnaryHistory v := unary_cont_closed uk uh hv
          have ur : UnaryHistory r' := unary_transport (unary_e1_closed uv) (hsame_symm same)
          exact ⟨v, hv, same, hsame_symm same, uv, ur⟩

theorem unary_shift_witness_result_unique_pair {k h r' : BHist} :
    UnaryHistory k → Cont k (.e1 h) r' →
      ∃ v : BHist, Cont k h v ∧ hsame r' (.e1 v) ∧
        (∀ {w : BHist}, Cont k h w → hsame v w) := by
  intro uk hr
  cases unary_shift_witness uk hr with
  | intro v shifted =>
      cases shifted with
      | intro hv same =>
          exact ⟨v, hv, same, by
            intro w hw
            exact cont_deterministic hv hw⟩

theorem unary_shift_witness_two_results_unique {k h r1 r2 : BHist} :
    UnaryHistory k → Cont k (BHist.e1 h) r1 → Cont k (BHist.e1 h) r2 →
      exists v1 : BHist, exists v2 : BHist,
        Cont k h v1 ∧ Cont k h v2 ∧ hsame v1 v2 ∧ hsame r1 r2 := by
  intro uk left right
  cases unary_shift_witness uk left with
  | intro v1 shiftedLeft =>
      cases shiftedLeft with
      | intro hv1 _ =>
          cases unary_shift_witness uk right with
          | intro v2 shiftedRight =>
              cases shiftedRight with
              | intro hv2 _ =>
                  exact ⟨v1, v2, hv1, hv2, cont_deterministic hv1 hv2,
                    cont_deterministic left right⟩

theorem unary_shift_witness_closed_unique_result {k h r' : BHist} :
    UnaryHistory k -> UnaryHistory h -> Cont k (BHist.e1 h) r' ->
      ∃ v : BHist, Cont k h v ∧ hsame r' (BHist.e1 v) ∧ UnaryHistory v ∧
        UnaryHistory r' ∧ (∀ {w : BHist}, Cont k h w -> hsame v w) := by
  intro uk uh hr
  cases unary_shift_unique_closed_witness uk uh hr with
  | intro v shifted =>
      cases shifted with
      | intro hv shiftedTail =>
          cases shiftedTail with
          | intro same closedTail =>
              cases closedTail with
              | intro uv unique =>
                  have ur : UnaryHistory r' :=
                    unary_transport (unary_e1_closed uv) (hsame_symm same)
                  exact ⟨v, hv, same, uv, ur, unique⟩

theorem unary_shift_witness_induction_closed_unique {k h r' : BHist} :
    UnaryHistory k -> UnaryHistory h -> Cont k (BHist.e1 h) r' ->
      exists v : BHist, Cont k h v ∧ hsame r' (BHist.e1 v) ∧ UnaryHistory v ∧
        UnaryHistory r' ∧ (forall {w : BHist}, Cont k h w -> hsame v w) := by
  intro uk uh hr
  cases unary_shift_witness uk hr with
  | intro v shifted =>
      cases shifted with
      | intro hv same =>
          have uv : UnaryHistory v := unary_cont_closed uk uh hv
          have ur : UnaryHistory r' := unary_transport (unary_e1_closed uv) (hsame_symm same)
          exact ⟨v, hv, same, uv, ur, by
            intro w hw
            exact cont_deterministic hv hw⟩

theorem unary_shift_step_closed_result_pair {k0 h r' : BHist} :
    UnaryHistory k0 → UnaryHistory h →
      (∀ {r : BHist}, Cont k0 (BHist.e1 h) r →
        ∃ v : BHist, Cont k0 h v ∧ hsame r (BHist.e1 v)) →
      Cont (BHist.e1 k0) (BHist.e1 h) r' →
      ∃ v : BHist,
        Cont (BHist.e1 k0) h v ∧ hsame r' (BHist.e1 v) ∧
          UnaryHistory v ∧ UnaryHistory r' := by
  intro uk uh shift hr'
  cases unary_shift_step_with_unary_result uk uh shift hr' with
  | intro v shifted =>
      cases shifted with
      | intro hv rest =>
          cases rest with
          | intro same uv =>
              have ur : UnaryHistory r' :=
                unary_transport (unary_e1_closed uv) (hsame_symm same)
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

theorem unary_shift_witness_by_induction_result_closed {k h r : BHist} :
    UnaryHistory k → UnaryHistory h → Cont k (BHist.e1 h) r →
      ∃ v : BHist, Cont k h v ∧ hsame r (BHist.e1 v) ∧
        UnaryHistory v ∧ UnaryHistory r := by
  intro uk uh hr
  cases unary_shift_witness_by_induction uk hr with
  | intro v shifted =>
      cases shifted with
      | intro hv same =>
          have uv : UnaryHistory v := unary_cont_closed uk uh hv
          have ur : UnaryHistory r := unary_transport (unary_e1_closed uv) (hsame_symm same)
          exact ⟨v, hv, same, uv, ur⟩

end BEDC.FKernel.Unary
