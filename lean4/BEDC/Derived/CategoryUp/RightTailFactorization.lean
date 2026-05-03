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

theorem ContinuationMorphism_comp_same_left_tail_factorization_deterministic {a b b' c c' : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c)
    (left' : ContinuationMorphism a b') (right' : ContinuationMorphism b' c')
    (sameLeft : hsame left.tail left'.tail)
    (sameComposite : hsame (append left.tail right.tail) (append left'.tail right'.tail)) :
    hsame b b' ∧ hsame right.tail right'.tail ∧ hsame c c' := by
  have sameMiddle : hsame b b' :=
    ContinuationMorphism_target_deterministic left left' sameLeft
  have sameRightTail : hsame right.tail right'.tail := by
    apply append_left_cancel (h := left.tail)
    exact sameComposite.trans (congrArg (fun tail => append tail right'.tail) sameLeft.symm)
  have transportedRight : Cont b' right.tail c :=
    cont_hsame_transport sameMiddle (hsame_refl right.tail) (hsame_refl c) right.rel
  have sameTarget : hsame c c' :=
    cont_deterministic transportedRight
      (cont_hsame_transport (hsame_refl b') (hsame_symm sameRightTail) (hsame_refl c') right'.rel)
  exact And.intro sameMiddle (And.intro sameRightTail sameTarget)

end BEDC.Derived.CategoryUp
