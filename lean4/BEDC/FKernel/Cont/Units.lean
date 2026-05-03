import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem append_left_unit_iff {h k : BHist} : append h k = k ↔ hsame h BHist.Empty := by
  constructor
  · intro eq
    induction k generalizing h with
    | Empty =>
        exact eq
    | e0 k ih =>
        exact ih (BHist.e0.inj eq)
    | e1 k ih =>
        exact ih (BHist.e1.inj eq)
  · intro hh
    cases hh
    exact append_empty_left k

theorem append_left_nonempty_self_absurd {h k : BHist} :
    (hsame h BHist.Empty -> False) -> hsame (append h k) k -> False := by
  intro hNonempty same
  exact hNonempty (append_right_cancel (k := k) (same.trans (append_empty_left k).symm))

theorem append_right_unit_iff {h k : BHist} : append h k = h ↔ hsame k BHist.Empty := by
  constructor
  · intro eq
    apply append_left_cancel (h := h)
    exact eq.trans (append_empty_right h).symm
  · intro hk
    cases hk
    exact append_empty_right h

theorem append_right_nonempty_self_absurd {h k : BHist} :
    (hsame k BHist.Empty -> False) -> hsame (append h k) h -> False := by
  intro kNonempty same
  exact kNonempty (append_left_cancel (h := h) (same.trans (append_empty_right h).symm))

theorem cont_right_unit_result {h r : BHist} : Cont h BHist.Empty r -> hsame r h := by
  intro hr
  exact hr

theorem cont_unit_laws_spine :
    (forall k : BHist, Cont BHist.Empty k k) /\
      (forall {h r : BHist}, Cont h BHist.Empty r -> hsame r h) := by
  exact cont_unit_laws

theorem cont_right_unit_proof_sprint : ∀ h : BHist, Cont h BHist.Empty h := by
  exact cont_right_unit

theorem cont_left_unit_induction_spine : ∀ k : BHist, Cont BHist.Empty k k := by
  intro k
  induction k with
  | Empty =>
      rfl
  | e0 k ih =>
      change BHist.e0 k = BHist.e0 (append BHist.Empty k)
      exact congrArg BHist.e0 ih
  | e1 k ih =>
      change BHist.e1 k = BHist.e1 (append BHist.Empty k)
      exact congrArg BHist.e1 ih

theorem cont_unit_uniqueness_pair :
    (∀ {h k : BHist}, Cont h k k → hsame h BHist.Empty) ∧
      (∀ {h k : BHist}, Cont h k h → hsame k BHist.Empty) := by
  constructor
  · intro h k hcont
    exact cont_left_unit_unique hcont
  · intro h k hcont
    exact cont_right_unit_unique hcont

theorem cont_unit_laws_with_uniqueness :
    (∀ h : BHist, Cont h BHist.Empty h) ∧
      (∀ h : BHist, Cont BHist.Empty h h) ∧
      (∀ {h r : BHist}, Cont h BHist.Empty r → hsame r h) ∧
      (∀ {h r : BHist}, Cont BHist.Empty h r → hsame r h) := by
  constructor
  · exact cont_right_unit
  · constructor
    · exact cont_left_unit
    · constructor
      · intro h r hcont
        exact cont_right_unit_result hcont
      · intro h r hcont
        exact cont_left_unit_result hcont

theorem cont_right_unit_law_endpoint_empty_iff {u : BHist} :
    ((∀ {d r : BHist}, Cont d u r -> hsame r d) ↔ hsame u BHist.Empty) := by
  constructor
  · intro law
    exact law (cont_left_unit u)
  · intro uEmpty
    intro d r hcont
    cases uEmpty
    exact Iff.mp cont_right_unit_iff hcont

theorem cont_left_unit_law_endpoint_empty_iff {u : BHist} :
    ((∀ {d r : BHist}, Cont u d r -> hsame r d) ↔ hsame u BHist.Empty) := by
  constructor
  · intro law
    exact law (cont_right_unit u)
  · intro uEmpty
    intro d r hcont
    cases uEmpty
    exact cont_left_unit_result hcont

theorem cont_step_result_iff_pair {h k r : BHist} :
    (Cont h (BHist.e0 k) (BHist.e0 r) ↔ Cont h k r) ∧
      (Cont h (BHist.e1 k) (BHist.e1 r) ↔ Cont h k r) := by
  constructor
  · constructor
    · intro hcont
      exact cont_step_rules_inversion_pair.left hcont
    · intro hcont
      exact cont_step_zero hcont
  · constructor
    · intro hcont
      exact cont_step_rules_inversion_pair.right hcont
    · intro hcont
      exact cont_step_one hcont

theorem cont_empty_result_iff {h k : BHist} :
    Cont h k BHist.Empty ↔ h = BHist.Empty /\ k = BHist.Empty := by
  constructor
  · intro hc
    exact append_eq_empty_iff.mp hc.symm
  · intro hk
    exact (append_eq_empty_iff.mpr hk).symm

theorem cont_e1_right_unit_probe_forces_empty {u : BHist} :
    (∀ {r : BHist}, Cont (BHist.e1 BHist.Empty) u r ->
      hsame r (BHist.e1 BHist.Empty)) -> hsame u BHist.Empty := by
  intro rightProbe
  have canonicalContinuation :
      Cont (BHist.e1 BHist.Empty) u (append (BHist.e1 BHist.Empty) u) :=
    cont_intro rfl
  have collapsedContinuation : Cont (BHist.e1 BHist.Empty) u (BHist.e1 BHist.Empty) :=
    cont_result_hsame_transport canonicalContinuation (rightProbe canonicalContinuation)
  exact cont_right_unit_unique collapsedContinuation

end BEDC.FKernel.Cont
