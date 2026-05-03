import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_left_tail_result_cases {a b c l : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame left.tail l ->
      (hsame right.tail BHist.Empty ∧
          hsame (ContinuationMorphism_comp_closed left right).tail l) ∨
        (∃ m : BHist,
          hsame right.tail (BHist.e0 m) ∧
            hsame (ContinuationMorphism_comp_closed left right).tail
              (BHist.e0 (append l m))) ∨
          (∃ m : BHist,
            hsame right.tail (BHist.e1 m) ∧
              hsame (ContinuationMorphism_comp_closed left right).tail
                (BHist.e1 (append l m))) := by
  intro sameLeftTail
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases sameLeftTail
          cases rightTail with
          | Empty =>
              left
              exact And.intro (hsame_refl BHist.Empty) (append_empty_right leftTail)
          | e0 m =>
              right
              left
              exact Exists.intro m
                (And.intro (hsame_refl (BHist.e0 m))
                  (hsame_refl (BHist.e0 (append leftTail m))))
          | e1 m =>
              right
              right
              exact Exists.intro m
                (And.intro (hsame_refl (BHist.e1 m))
                  (hsame_refl (BHist.e1 (append leftTail m))))

end BEDC.Derived.CategoryUp
