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

theorem ContinuationMorphism_e0_tail_target_not_empty {a b m : BHist}
    (morph : ContinuationMorphism a b) :
    hsame morph.tail (BHist.e0 m) -> hsame b BHist.Empty -> False := by
  intro sameTail sameTarget
  cases ContinuationMorphism_right_e0_tail_target_cases morph sameTail with
  | intro r targetCases =>
      cases targetCases.left
      exact not_hsame_e0_empty sameTarget

end BEDC.Derived.CategoryUp
