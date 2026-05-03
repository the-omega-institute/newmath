import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist BEDC.FKernel.Unary

theorem ContinuationMorphism_comp_unary_tail_e0_absurd {a b c z : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    UnaryHistory left.tail -> UnaryHistory right.tail ->
      hsame (ContinuationMorphism_comp_closed left right).tail (BHist.e0 z) -> False := by
  intro leftCarrier rightCarrier sameTail
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          exact unary_history_hsame_zero_absurd
            (unary_append_closed leftCarrier rightCarrier) sameTail

end BEDC.Derived.CategoryUp
