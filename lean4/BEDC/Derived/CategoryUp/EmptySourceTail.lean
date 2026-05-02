import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_empty_source_tail_target_hsame {target : BHist}
    (m : ContinuationMorphism BHist.Empty target) : hsame m.tail target := by
  cases m with
  | mk tail rel =>
      exact hsame_symm (cont_left_unit_result rel)

end BEDC.Derived.CategoryUp
