import BEDC.Derived.CommRingUp.SignedProductBalance

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem commring_parallelogram_square_sum {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {a b : BHist} :
    hsame (add (mul (add a b) (add a b)) (mul (add a (neg b)) (add a (neg b))))
      (add (add (mul a a) (mul a a)) (add (mul b b) (mul b b))) := by
  have addRightZero : forall x : BHist, hsame (add x BHist.Empty) x := by
    exact BEDC.Derived.RingUp.ring_add_right_zero addComm zeroLeft
  have addRightInverse : forall x : BHist, hsame (add x (neg x)) BHist.Empty := by
    exact BEDC.Derived.RingUp.ring_add_right_inverse addComm negLeft
  let aa := mul a a
  let ab := mul a b
  let bb := mul b b
  let nab := neg ab
  let doubledA := add aa aa
  let doubledB := add bb bb
  let mixedZero := add ab nab
  have positiveSquare :
      hsame (mul (add a b) (add a b))
        (add (add aa ab) (add ab bb)) := by
    exact commring_square_add_expand mulComm addCongr leftDistrib rightDistrib a b
  have signedSquare :
      hsame (mul (add a (neg b)) (add a (neg b)))
        (add (add aa nab) (add nab bb)) := by
    exact commring_square_signed_difference_expand addAssoc addComm zeroLeft negLeft addCongr
      mulComm mulCongr leftDistrib rightDistrib
  have expanded :
      hsame (add (mul (add a b) (add a b)) (mul (add a (neg b)) (add a (neg b))))
        (add (add (add aa ab) (add ab bb)) (add (add aa nab) (add nab bb))) := by
    exact addCongr positiveSquare signedSquare
  have rowsInterchanged :
      hsame (add (add (add aa ab) (add ab bb)) (add (add aa nab) (add nab bb)))
        (add (add (add aa ab) (add aa nab)) (add (add ab bb) (add nab bb))) := by
    exact BEDC.Derived.AbGroupUp.abgroup_mul_middle_four addAssoc addComm addCongr
      (add aa ab) (add ab bb) (add aa nab) (add nab bb)
  have collectLeft :
      hsame (add (add aa ab) (add aa nab)) (add doubledA mixedZero) := by
    exact BEDC.Derived.AbGroupUp.abgroup_mul_middle_four addAssoc addComm addCongr
      aa ab aa nab
  have collectRight :
      hsame (add (add ab bb) (add nab bb)) (add mixedZero doubledB) := by
    exact BEDC.Derived.AbGroupUp.abgroup_mul_middle_four addAssoc addComm addCongr
      ab bb nab bb
  have collected :
      hsame (add (add (add aa ab) (add aa nab)) (add (add ab bb) (add nab bb)))
        (add (add doubledA mixedZero) (add mixedZero doubledB)) := by
    exact addCongr collectLeft collectRight
  have mixedZeroEmpty : hsame mixedZero BHist.Empty := by
    exact addRightInverse ab
  have eraseMixed :
      hsame (add (add doubledA mixedZero) (add mixedZero doubledB))
        (add (add doubledA BHist.Empty) (add BHist.Empty doubledB)) := by
    exact addCongr (addCongr (hsame_refl doubledA) mixedZeroEmpty)
      (addCongr mixedZeroEmpty (hsame_refl doubledB))
  have eraseEmptyTerms :
      hsame (add (add doubledA BHist.Empty) (add BHist.Empty doubledB))
        (add doubledA doubledB) := by
    exact addCongr (addRightZero doubledA) (zeroLeft doubledB)
  exact hsame_trans expanded
    (hsame_trans rowsInterchanged
      (hsame_trans collected (hsame_trans eraseMixed eraseEmptyTerms)))

end BEDC.Derived.CommRingUp
