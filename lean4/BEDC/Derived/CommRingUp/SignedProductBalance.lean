import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem commring_signed_product_balance {add mul : BHist -> BHist -> BHist}
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
    {a b c d : BHist} :
    hsame (add (mul (add a (neg b)) (add c (neg d))) (add (mul a d) (mul b c)))
      (add (mul a c) (mul b d)) := by
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have addRightZero : forall x : BHist, hsame (add x BHist.Empty) x := by
    exact BEDC.Derived.RingUp.ring_add_right_zero addComm zeroLeft
  have collapseRightSub :
      forall x y : BHist, hsame (add (add x (neg y)) y) x := by
    intro x y
    have reassoc : hsame (add (add x (neg y)) y) (add x (add (neg y) y)) := by
      exact addAssoc x (neg y) y
    have cancel : hsame (add x (add (neg y) y)) (add x BHist.Empty) := by
      exact addCongr (hsame_refl x) (negLeft y)
    exact hsame_trans reassoc (hsame_trans cancel (addRightZero x))
  have collapseLeftSub :
      forall x y : BHist, hsame (add (add (neg x) y) x) y := by
    intro x y
    have reassoc : hsame (add (add (neg x) y) x) (add (neg x) (add y x)) := by
      exact addAssoc (neg x) y x
    have swapTail : hsame (add y x) (add x y) := by
      exact addComm y x
    have transport : hsame (add (neg x) (add y x)) (add (neg x) (add x y)) := by
      exact addCongr (hsame_refl (neg x)) swapTail
    have reassocBack :
        hsame (add (neg x) (add x y)) (add (add (neg x) x) y) := by
      exact hsame_symm (addAssoc (neg x) x y)
    have cancel : hsame (add (add (neg x) x) y) (add BHist.Empty y) := by
      exact addCongr (negLeft x) (hsame_refl y)
    exact hsame_trans reassoc
      (hsame_trans transport (hsame_trans reassocBack (hsame_trans cancel (zeroLeft y))))
  have signedNormal :
      hsame (mul (add a (neg b)) (add c (neg d)))
        (add (add (mul a c) (neg (mul a d))) (add (neg (mul b c)) (mul b d))) := by
    exact commring_signed_binary_product_normal_form addAssoc addComm zeroLeft negLeft
      mulComm addCongr mulCongr leftDistrib rightDistrib a b c d
  have transportSigned :
      hsame (add (mul (add a (neg b)) (add c (neg d))) (add (mul a d) (mul b c)))
        (add
          (add (add (mul a c) (neg (mul a d))) (add (neg (mul b c)) (mul b d)))
          (add (mul a d) (mul b c))) := by
    exact addCongr signedNormal (hsame_refl (add (mul a d) (mul b c)))
  have regroup :
      hsame
        (add
          (add (add (mul a c) (neg (mul a d))) (add (neg (mul b c)) (mul b d)))
          (add (mul a d) (mul b c)))
        (add (add (add (mul a c) (neg (mul a d))) (mul a d))
          (add (add (neg (mul b c)) (mul b d)) (mul b c))) := by
    exact BEDC.Derived.AbGroupUp.abgroup_mul_middle_four addAssoc addComm addCongr
      (add (mul a c) (neg (mul a d))) (add (neg (mul b c)) (mul b d))
      (mul a d) (mul b c)
  have collapse :
      hsame
        (add (add (add (mul a c) (neg (mul a d))) (mul a d))
          (add (add (neg (mul b c)) (mul b d)) (mul b c)))
        (add (mul a c) (mul b d)) := by
    exact addCongr (collapseRightSub (mul a c) (mul a d))
      (collapseLeftSub (mul b c) (mul b d))
  exact hsame_trans transportSigned (hsame_trans regroup collapse)

theorem commring_signed_product_empty_zero_exact {add mul : BHist -> BHist -> BHist}
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
    {a b c d : BHist} :
    hsame (mul (add a (neg b)) (add c (neg d))) BHist.Empty <->
      hsame (add (mul a c) (mul b d)) (add (mul a d) (mul b c)) := by
  have balance := commring_signed_product_balance addAssoc addComm zeroLeft negLeft addCongr
    mulComm mulCongr leftDistrib (a := a) (b := b) (c := c) (d := d)
  have addRightZero : forall x : BHist, hsame (add x BHist.Empty) x := by
    exact BEDC.Derived.RingUp.ring_add_right_zero addComm zeroLeft
  have addRightInverse : forall x : BHist, hsame (add x (neg x)) BHist.Empty := by
    exact BEDC.Derived.RingUp.ring_add_right_inverse addComm negLeft
  constructor
  · intro productEmpty
    have transported :
        hsame
          (add (mul (add a (neg b)) (add c (neg d))) (add (mul a d) (mul b c)))
          (add BHist.Empty (add (mul a d) (mul b c))) := by
      exact addCongr productEmpty (hsame_refl (add (mul a d) (mul b c)))
    exact hsame_trans (hsame_symm balance) (hsame_trans transported
      (zeroLeft (add (mul a d) (mul b c))))
  · intro crossSame
    have sameProducts :
        hsame
          (add (mul (add a (neg b)) (add c (neg d))) (add (mul a d) (mul b c)))
          (add BHist.Empty (add (mul a d) (mul b c))) := by
      exact hsame_trans balance (hsame_trans crossSame
        (hsame_symm (zeroLeft (add (mul a d) (mul b c)))))
    exact BEDC.Derived.GroupUp.group_right_cancel
      addAssoc addRightZero addCongr addRightInverse sameProducts

end BEDC.Derived.CommRingUp
