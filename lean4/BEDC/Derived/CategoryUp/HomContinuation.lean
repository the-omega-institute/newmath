import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ContinuationMorphism_comp_tail_CategoryHomCarrier {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    UnaryHistory a -> UnaryHistory c -> UnaryHistory left.tail -> UnaryHistory right.tail ->
      CategoryHomCarrier a c (ContinuationMorphism_comp_closed left right).tail := by
  intro sourceCarrier targetCarrier leftTailCarrier rightTailCarrier
  exact And.intro sourceCarrier
    (And.intro targetCarrier
      (And.intro
        (unary_append_closed leftTailCarrier rightTailCarrier)
        (ContinuationMorphism_comp_closed left right).rel))

theorem ContinuationMorphism_comp_tail_CategoryHomCarrier_iff {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    CategoryHomCarrier a c (ContinuationMorphism_comp_closed left right).tail <->
      UnaryHistory a /\ UnaryHistory c /\ UnaryHistory left.tail /\ UnaryHistory right.tail := by
  constructor
  · intro homCarrier
    cases left with
    | mk leftTail leftRel =>
        cases right with
        | mk rightTail rightRel =>
            exact And.intro homCarrier.left
              (And.intro homCarrier.right.left
                (And.intro
                  (unary_append_left_factor homCarrier.right.right.left)
                  (unary_append_right_factor homCarrier.right.right.left)))
  · intro factors
    exact ContinuationMorphism_comp_tail_CategoryHomCarrier left right
      factors.left factors.right.left factors.right.right.left factors.right.right.right

theorem ContinuationMorphism_comp_tail_CategoryHomCarrier_factors_iff {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    CategoryHomCarrier a c (ContinuationMorphism_comp_closed left right).tail <->
      UnaryHistory a /\ UnaryHistory c /\
        CategoryHomCarrier a b left.tail /\ CategoryHomCarrier b c right.tail := by
  constructor
  · intro homCarrier
    cases left with
    | mk leftTail leftRel =>
        cases right with
        | mk rightTail rightRel =>
            have leftTailCarrier : UnaryHistory leftTail :=
              unary_append_left_factor homCarrier.right.right.left
            have rightTailCarrier : UnaryHistory rightTail :=
              unary_append_right_factor homCarrier.right.right.left
            have middleCarrier : UnaryHistory b :=
              unary_cont_closed homCarrier.left leftTailCarrier leftRel
            exact And.intro homCarrier.left
              (And.intro homCarrier.right.left
                (And.intro
                  (And.intro homCarrier.left
                    (And.intro middleCarrier (And.intro leftTailCarrier leftRel)))
                  (And.intro middleCarrier
                    (And.intro homCarrier.right.left (And.intro rightTailCarrier rightRel)))))
  · intro factors
    exact ContinuationMorphism_comp_tail_CategoryHomCarrier left right
      factors.left factors.right.left
      factors.right.right.left.right.right.left
      factors.right.right.right.right.right.left

end BEDC.Derived.CategoryUp
