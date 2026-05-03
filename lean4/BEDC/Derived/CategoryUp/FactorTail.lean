import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_right_factor_tail_hsame {a b c r : BHist}
    (left : ContinuationMorphism a b) (composite : ContinuationMorphism a c)
    (tailRel : Cont left.tail r composite.tail) (right : ContinuationMorphism b c) :
    hsame r right.tail := by
  cases left with
  | mk leftTail leftRel =>
      cases composite with
      | mk compositeTail compositeRel =>
          cases right with
          | mk rightTail rightRel =>
              have recovered : Cont b r c := by
                cases leftRel
                cases tailRel
                exact cont_intro (compositeRel.trans (append_assoc a leftTail r).symm)
              exact cont_left_cancel recovered rightRel

theorem ContinuationMorphism_comp_left_factor_tail_hsame {a b c l : BHist}
    (right : ContinuationMorphism b c) (composite : ContinuationMorphism a c)
    (tailRel : Cont l right.tail composite.tail) (left : ContinuationMorphism a b) :
    hsame l left.tail := by
  cases right with
  | mk rightTail rightRel =>
      cases composite with
      | mk compositeTail compositeRel =>
          cases left with
          | mk leftTail leftRel =>
              have recovered : Cont a l b :=
                cont_composite_left_factor rightRel tailRel compositeRel
              exact cont_left_cancel recovered leftRel

theorem ContinuationMorphism_comp_middle_tail_readback {a b b' c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b' c)
    (composite : ContinuationMorphism a c)
    (tailRel : Cont left.tail right.tail composite.tail) :
    hsame b b' ∧ hsame (append left.tail right.tail) composite.tail := by
  cases left with
  | mk leftTail leftRel =>
      cases composite with
      | mk compositeTail compositeRel =>
          have recoveredRel : Cont b right.tail c := by
            cases leftRel
            cases tailRel
            exact cont_intro (compositeRel.trans (append_assoc a leftTail right.tail).symm)
          have sameMiddle : hsame b b' :=
            cont_right_cancel recoveredRel right.rel
          exact And.intro sameMiddle tailRel.symm

theorem ContinuationMorphism_comp_right_factor_reconstructs {a b c r : BHist}
    (left : ContinuationMorphism a b) (composite : ContinuationMorphism a c)
    (tailRel : Cont left.tail r composite.tail) :
    hsame (ContinuationMorphism_comp_closed left
      (ContinuationMorphism_comp_right_factor left composite tailRel)).tail composite.tail := by
  exact tailRel.symm

theorem ContinuationMorphism_comp_left_factor_reconstructs {a b c l : BHist}
    (right : ContinuationMorphism b c) (composite : ContinuationMorphism a c)
    (tailRel : Cont l right.tail composite.tail) :
    hsame (ContinuationMorphism_comp_closed
      (ContinuationMorphism_comp_left_factor right composite tailRel) right).tail
      composite.tail := by
  have displayed :
      hsame (append l right.tail) composite.tail :=
    tailRel.symm
  exact displayed

theorem ContinuationMorphism_tail_factorization_iff {a c l r t : BHist} :
    Cont l r t ->
      ((∃ composite : ContinuationMorphism a c, hsame composite.tail t) ↔
        ∃ b : BHist,
          (∃ left : ContinuationMorphism a b, hsame left.tail l) ∧
            (∃ right : ContinuationMorphism b c, hsame right.tail r)) := by
  intro split
  constructor
  · intro compositeData
    cases compositeData with
    | intro composite sameTail =>
        refine Exists.intro (append a l) ?_
        constructor
        · exact Exists.intro { tail := l, rel := cont_intro rfl } (hsame_refl l)
        · refine Exists.intro { tail := r, rel := ?_ } (hsame_refl r)
          cases composite with
          | mk compositeTail compositeRel =>
              cases split
              cases sameTail
              exact cont_intro (compositeRel.trans (append_assoc a l r).symm)
  · intro factorData
    cases factorData with
    | intro b factors =>
        cases factors.left with
        | intro left sameLeft =>
            cases factors.right with
            | intro right sameRight =>
                let composite := ContinuationMorphism_comp_closed left right
                refine Exists.intro composite ?_
                have compositeSplit : Cont left.tail right.tail composite.tail := by
                  cases left
                  cases right
                  exact cont_intro rfl
                exact cont_respects_hsame sameLeft sameRight
                  compositeSplit split

end BEDC.Derived.CategoryUp
