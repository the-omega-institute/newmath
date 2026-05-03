import BEDC.Derived.CategoryUp.VisibleTailResult

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_right_visible_tail_empty_absurd {a b c m : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    (hsame right.tail (BHist.e0 m) ->
      hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty -> False) ∧
    (hsame right.tail (BHist.e1 m) ->
      hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty -> False) := by
  constructor
  · intro sameRightTail compositeEmpty
    cases left with
    | mk leftTail leftRel =>
        cases right with
        | mk rightTail rightRel =>
            cases sameRightTail
            exact not_hsame_e0_empty (append_eq_empty_iff.mp compositeEmpty).right
  · intro sameRightTail compositeEmpty
    cases left with
    | mk leftTail leftRel =>
        cases right with
        | mk rightTail rightRel =>
            cases sameRightTail
            exact not_hsame_e1_empty (append_eq_empty_iff.mp compositeEmpty).right

end BEDC.Derived.CategoryUp
