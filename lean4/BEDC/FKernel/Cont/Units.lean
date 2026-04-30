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

theorem cont_right_unit_result {h r : BHist} : Cont h BHist.Empty r -> hsame r h := by
  intro hr
  exact hr

end BEDC.FKernel.Cont
