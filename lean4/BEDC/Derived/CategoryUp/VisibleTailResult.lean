import BEDC.Derived.CategoryUp.CompositeEmptyTail

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

theorem ContinuationMorphism_comp_right_visible_tail_result_cases {a b c m : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame right.tail (BHist.e1 m) ->
      ∃ k : BHist,
        hsame (ContinuationMorphism_comp_closed left right).tail (BHist.e1 k) ∧
          Cont left.tail m k := by
  intro sameRightTail
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases sameRightTail
          exact Exists.intro (append leftTail m)
            (And.intro (hsame_refl (BHist.e1 (append leftTail m))) (cont_intro rfl))

theorem ContinuationMorphism_comp_right_e0_tail_result_cases {a b c m : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame right.tail (BHist.e0 m) ->
      ∃ k : BHist,
        hsame (ContinuationMorphism_comp_closed left right).tail (BHist.e0 k) ∧
          Cont left.tail m k := by
  intro sameRightTail
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases sameRightTail
          exact Exists.intro (append leftTail m)
            (And.intro (hsame_refl (BHist.e0 (append leftTail m))) (cont_intro rfl))

theorem ContinuationMorphism_comp_right_e0_tail_result_not_empty {a b c m : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame right.tail (BHist.e0 m) ->
      hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty -> False := by
  intro sameRightTail compositeEmpty
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases sameRightTail
          exact not_hsame_e0_empty compositeEmpty

theorem ContinuationMorphism_comp_e1_tail_left_cases {a b c k : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c)
    (sameComposite : hsame (ContinuationMorphism_comp_closed left right).tail (BHist.e1 k))
    (leftCarrier : UnaryHistory left.tail) :
    (hsame left.tail BHist.Empty ∧ hsame right.tail (BHist.e1 k)) ∨
      (∃ l : BHist, hsame left.tail (BHist.e1 l) ∧
        Cont (BHist.e1 l) right.tail (BHist.e1 k)) := by
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases leftTail with
          | Empty =>
              left
              exact And.intro (hsame_refl BHist.Empty)
                ((append_empty_left rightTail).symm.trans sameComposite)
          | e0 leftTail =>
              exact False.elim (unary_no_zero_extension leftCarrier)
          | e1 leftTail =>
              right
              exact Exists.intro leftTail
                (And.intro (hsame_refl (BHist.e1 leftTail)) (cont_intro sameComposite.symm))

theorem ContinuationMorphism_comp_e1_tail_right_cases {a b c k : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c)
    (sameComposite : hsame (ContinuationMorphism_comp_closed left right).tail (BHist.e1 k))
    (rightCarrier : UnaryHistory right.tail) :
    (hsame right.tail BHist.Empty ∧ hsame left.tail (BHist.e1 k)) ∨
      (Exists (fun m : BHist => hsame right.tail (BHist.e1 m) ∧
        Cont left.tail (BHist.e1 m) (BHist.e1 k))) := by
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases rightTail with
          | Empty =>
              left
              exact And.intro (hsame_refl BHist.Empty)
                ((append_empty_right leftTail).symm.trans sameComposite)
          | e0 rightTail =>
              exact False.elim (unary_no_zero_extension rightCarrier)
          | e1 rightTail =>
              right
              exact Exists.intro rightTail
                (And.intro (hsame_refl (BHist.e1 rightTail)) (cont_intro sameComposite.symm))

theorem ContinuationMorphism_comp_nonempty_e1_tail_factors {a b c k : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c)
    (sameComposite : hsame (ContinuationMorphism_comp_closed left right).tail (BHist.e1 k))
    (leftCarrier : UnaryHistory left.tail) (rightCarrier : UnaryHistory right.tail)
    (leftNonempty : hsame left.tail BHist.Empty -> False)
    (rightNonempty : hsame right.tail BHist.Empty -> False) :
    ∃ l m : BHist, hsame left.tail (BHist.e1 l) ∧ hsame right.tail (BHist.e1 m) ∧
      Cont (BHist.e1 l) (BHist.e1 m) (BHist.e1 k) := by
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases leftTail with
          | Empty =>
              exact False.elim (leftNonempty (hsame_refl BHist.Empty))
          | e0 leftTail =>
              exact False.elim (unary_no_zero_extension leftCarrier)
          | e1 leftTail =>
              cases rightTail with
              | Empty =>
                  exact False.elim (rightNonempty (hsame_refl BHist.Empty))
              | e0 rightTail =>
                  exact False.elim (unary_no_zero_extension rightCarrier)
              | e1 rightTail =>
                  exact Exists.intro leftTail
                    (Exists.intro rightTail
                      (And.intro (hsame_refl (BHist.e1 leftTail))
                        (And.intro (hsame_refl (BHist.e1 rightTail))
                          (cont_intro sameComposite.symm))))

end BEDC.Derived.CategoryUp
