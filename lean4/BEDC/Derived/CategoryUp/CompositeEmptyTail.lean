import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_empty_tail_inversion {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty ->
      hsame left.tail BHist.Empty ∧ hsame right.tail BHist.Empty ∧ hsame a b ∧ hsame b c := by
  intro compositeEmpty
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          have emptyParts : leftTail = BHist.Empty ∧ rightTail = BHist.Empty :=
            append_eq_empty_iff.mp compositeEmpty
          cases emptyParts.left
          cases emptyParts.right
          exact
            And.intro (hsame_refl BHist.Empty)
              (And.intro (hsame_refl BHist.Empty)
                (And.intro
                  (cont_deterministic (cont_right_unit a) leftRel)
                  (cont_deterministic (cont_right_unit b) rightRel)))

theorem ContinuationMorphism_comp_tail_empty_iff {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty ↔
      hsame left.tail BHist.Empty ∧ hsame right.tail BHist.Empty := by
  constructor
  · intro compositeEmpty
    have parts := ContinuationMorphism_comp_empty_tail_inversion left right compositeEmpty
    exact And.intro parts.left parts.right.left
  · intro parts
    cases left with
    | mk leftTail leftRel =>
        cases right with
        | mk rightTail rightRel =>
            cases parts.left
            cases parts.right
            exact hsame_refl BHist.Empty

theorem ContinuationMorphism_comp_tail_cont {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    Cont left.tail right.tail (ContinuationMorphism_comp_closed left right).tail ∧
      Cont a (ContinuationMorphism_comp_closed left right).tail c := by
  constructor
  · cases left with
    | mk leftTail leftRel =>
        cases right with
        | mk rightTail rightRel =>
            exact cont_intro rfl
  · exact (ContinuationMorphism_comp_closed left right).rel

end BEDC.Derived.CategoryUp
