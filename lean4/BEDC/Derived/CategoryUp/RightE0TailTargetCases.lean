import BEDC.Derived.CategoryUp
import BEDC.FKernel.Cont.Step

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_right_e0_tail_target_cases {b c m : BHist}
    (right : ContinuationMorphism b c) :
    hsame right.tail (BHist.e0 m) -> ∃ r : BHist, c = BHist.e0 r ∧ Cont b m r := by
  intro sameTail
  cases right with
  | mk tail rel =>
      cases sameTail
      exact cont_e0_result_witness rel

end BEDC.Derived.CategoryUp
