import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_empty_target_inversion {source : BHist}
    (m : ContinuationMorphism source BHist.Empty) :
    hsame source BHist.Empty ∧ hsame m.tail BHist.Empty := by
  cases m with
  | mk tail rel =>
      exact cont_empty_result_inversion rel

end BEDC.Derived.CategoryUp
