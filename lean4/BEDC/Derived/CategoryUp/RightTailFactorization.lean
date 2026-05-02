import BEDC.Derived.CategoryUp.CompositeEmptyTail

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_same_right_tail_factorization_deterministic
    {a a' b b' c : BHist} (left : ContinuationMorphism a b)
    (right : ContinuationMorphism b c) (left' : ContinuationMorphism a' b')
    (right' : ContinuationMorphism b' c) (sameRightTail : hsame right.tail right'.tail)
    (sameCompositeTail :
      hsame (ContinuationMorphism_comp_closed left right).tail
        (ContinuationMorphism_comp_closed left' right').tail) :
    Cont left.tail right.tail (ContinuationMorphism_comp_closed left right).tail ∧
      Cont left'.tail right'.tail (ContinuationMorphism_comp_closed left' right').tail ∧
        hsame a a' ∧ hsame b b' ∧ hsame left.tail left'.tail := by
  have leftCompTail := ContinuationMorphism_comp_tail_cont left right
  have rightCompTail := ContinuationMorphism_comp_tail_cont left' right'
  have sameSource : hsame a a' :=
    ContinuationMorphism_source_deterministic
      (ContinuationMorphism_comp_closed left right)
      (ContinuationMorphism_comp_closed left' right') sameCompositeTail
  have sameMiddle : hsame b b' :=
    ContinuationMorphism_source_deterministic right right' sameRightTail
  have transportedLeft :
      Cont a' left.tail b' :=
    cont_hsame_transport sameSource (hsame_refl left.tail) sameMiddle left.rel
  have sameLeftTail : hsame left.tail left'.tail :=
    cont_left_cancel transportedLeft left'.rel
  exact
    And.intro leftCompTail.left
      (And.intro rightCompTail.left
        (And.intro sameSource (And.intro sameMiddle sameLeftTail)))

end BEDC.Derived.CategoryUp
