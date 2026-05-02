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

end BEDC.Derived.CategoryUp
