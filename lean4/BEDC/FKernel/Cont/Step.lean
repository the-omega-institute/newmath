import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_determinacy_up_to_hsame_spine {h k r r' : BHist} :
    Cont h k r -> Cont h k r' -> hsame r r' := by
  intro left right
  exact cont_deterministic left right

theorem cont_e0_result_witness {h k r : BHist} :
    Cont h (BHist.e0 k) r -> exists r0 : BHist, r = BHist.e0 r0 /\ Cont h k r0 := by
  intro hcont
  exact cont_step_result_inversions.left hcont

theorem cont_e1_result_witness {h k r : BHist} :
    Cont h (BHist.e1 k) r -> exists r0 : BHist, r = BHist.e1 r0 /\ Cont h k r0 := by
  intro hcont
  exact cont_step_result_inversions.right hcont

theorem cont_step_zero_iff {h k r : BHist} :
    Cont h (BHist.e0 k) (BHist.e0 r) ↔ Cont h k r := by
  constructor
  · intro hcont
    exact cont_step_rules_inversion_pair.left hcont
  · intro hcont
    exact cont_step_zero hcont

theorem cont_step_one_iff {h k r : BHist} :
    Cont h (BHist.e1 k) (BHist.e1 r) ↔ Cont h k r := by
  constructor
  · intro hcont
    exact cont_step_rules_inversion_pair.right hcont
  · intro hcont
    exact cont_step_one hcont

theorem cont_step_rules_iff_pair :
    (∀ {h k r : BHist}, Cont h (BHist.e0 k) (BHist.e0 r) ↔ Cont h k r) ∧
      (∀ {h k r : BHist}, Cont h (BHist.e1 k) (BHist.e1 r) ↔ Cont h k r) := by
  constructor
  · exact cont_step_zero_iff
  · exact cont_step_one_iff

theorem continuation_step_rules_iff_pair :
    (forall {h k r : BHist}, Cont h (BHist.e0 k) (BHist.e0 r) <-> Cont h k r) /\
      (forall {h k r : BHist}, Cont h (BHist.e1 k) (BHist.e1 r) <-> Cont h k r) := by
  exact cont_step_rules_iff_pair

end BEDC.FKernel.Cont
