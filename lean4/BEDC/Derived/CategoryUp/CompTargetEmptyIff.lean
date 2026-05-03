import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_target_empty_iff {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame c BHist.Empty ↔
      hsame a BHist.Empty ∧ hsame b BHist.Empty ∧ hsame left.tail BHist.Empty ∧
        hsame right.tail BHist.Empty := by
  constructor
  · intro sameTarget
    exact ContinuationMorphism_comp_empty_target_inversion left
      { tail := right.tail, rel := cont_result_hsame_transport right.rel sameTarget }
  · intro endpoints
    cases right with
    | mk rightTail rightRel =>
        cases endpoints.right.left
        cases endpoints.right.right.right
        cases rightRel
        exact hsame_refl BHist.Empty

end BEDC.Derived.CategoryUp
