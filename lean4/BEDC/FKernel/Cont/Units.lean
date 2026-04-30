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

theorem append_right_unit_iff {h k : BHist} : append h k = h ↔ hsame k BHist.Empty := by
  constructor
  · intro eq
    apply append_left_cancel (h := h)
    exact eq.trans (append_empty_right h).symm
  · intro hk
    cases hk
    exact append_empty_right h

theorem cont_right_unit_result {h r : BHist} : Cont h BHist.Empty r -> hsame r h := by
  intro hr
  exact hr

theorem cont_unit_laws_spine :
    (forall k : BHist, Cont BHist.Empty k k) /\
      (forall {h r : BHist}, Cont h BHist.Empty r -> hsame r h) := by
  exact cont_unit_laws

theorem cont_unit_uniqueness_pair :
    (∀ {h k : BHist}, Cont h k k → hsame h BHist.Empty) ∧
      (∀ {h k : BHist}, Cont h k h → hsame k BHist.Empty) := by
  constructor
  · intro h k hcont
    exact cont_left_unit_unique hcont
  · intro h k hcont
    exact cont_right_unit_unique hcont

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

end BEDC.FKernel.Cont
