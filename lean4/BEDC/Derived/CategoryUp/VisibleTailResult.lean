import BEDC.Derived.CategoryUp.CompositeEmptyTail

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_visible_tails_result_cases {a b c l m : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame left.tail (BHist.e1 l) -> hsame right.tail (BHist.e1 m) ->
      ∃ k : BHist,
        hsame (ContinuationMorphism_comp_closed left right).tail (BHist.e1 k) ∧
          Cont (BHist.e1 l) m k := by
  intro sameLeftTail sameRightTail
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases sameLeftTail
          cases sameRightTail
          exact Exists.intro (append (BHist.e1 l) m)
            (And.intro (hsame_refl (BHist.e1 (append (BHist.e1 l) m))) (cont_intro rfl))

theorem ContinuationMorphism_comp_visible_tails_result_not_empty {a b c l m : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame left.tail (BHist.e1 l) -> hsame right.tail (BHist.e1 m) ->
      hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty -> False := by
  intro sameLeftTail sameRightTail compositeEmpty
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases sameLeftTail
          cases sameRightTail
          exact not_hsame_e1_empty compositeEmpty

end BEDC.Derived.CategoryUp
