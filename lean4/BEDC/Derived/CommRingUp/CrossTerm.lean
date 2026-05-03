import BEDC.Derived.CommRingUp.SignedProductBalance

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem commring_square_cross_term_extraction_pair {add mul : BHist -> BHist -> BHist}
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
    {a b : BHist} :
    hsame
        (add (mul (add a b) (add a b))
          (add (neg (mul a a)) (neg (mul b b))))
        (add (mul a b) (mul a b)) ∧
      hsame
        (add (mul (add a (neg b)) (add a (neg b)))
          (add (neg (mul a a)) (neg (mul b b))))
        (add (neg (mul a b)) (neg (mul a b))) := by
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have addRightZero : forall x : BHist, hsame (add x BHist.Empty) x := by
    exact BEDC.Derived.RingUp.ring_add_right_zero addComm zeroLeft
  have addRightInverse : forall x : BHist, hsame (add x (neg x)) BHist.Empty := by
    exact BEDC.Derived.RingUp.ring_add_right_inverse addComm negLeft
  have collapseHead :
      forall x y : BHist, hsame (add (add x y) (neg x)) y := by
    intro x y
    have reassoc : hsame (add (add x y) (neg x)) (add x (add y (neg x))) := by
      exact addAssoc x y (neg x)
    have swapInner : hsame (add y (neg x)) (add (neg x) y) := by
      exact addComm y (neg x)
    have transport : hsame (add x (add y (neg x))) (add x (add (neg x) y)) := by
      exact addCongr (hsame_refl x) swapInner
    have reassocBack : hsame (add x (add (neg x) y)) (add (add x (neg x)) y) := by
      exact hsame_symm (addAssoc x (neg x) y)
    have cancel : hsame (add (add x (neg x)) y) (add BHist.Empty y) := by
      exact addCongr (addRightInverse x) (hsame_refl y)
    exact hsame_trans reassoc
      (hsame_trans transport
        (hsame_trans reassocBack (hsame_trans cancel (zeroLeft y))))
  have collapseTail :
      forall x y : BHist, hsame (add (add y x) (neg x)) y := by
    intro x y
    have reassoc : hsame (add (add y x) (neg x)) (add y (add x (neg x))) := by
      exact addAssoc y x (neg x)
    have cancel : hsame (add y (add x (neg x))) (add y BHist.Empty) := by
      exact addCongr (hsame_refl y) (addRightInverse x)
    exact hsame_trans reassoc (hsame_trans cancel (addRightZero y))
  have positive :
      hsame
        (add (mul (add a b) (add a b))
          (add (neg (mul a a)) (neg (mul b b))))
        (add (mul a b) (mul a b)) := by
    have expanded :
        hsame
          (add (mul (add a b) (add a b))
            (add (neg (mul a a)) (neg (mul b b))))
          (add
            (add (add (mul a a) (mul a b)) (add (mul a b) (mul b b)))
            (add (neg (mul a a)) (neg (mul b b)))) := by
      exact addCongr
        (commring_square_add_expand mulComm addCongr leftDistrib rightDistrib a b)
        (hsame_refl (add (neg (mul a a)) (neg (mul b b))))
    have regroup :
        hsame
          (add
            (add (add (mul a a) (mul a b)) (add (mul a b) (mul b b)))
            (add (neg (mul a a)) (neg (mul b b))))
          (add
            (add (add (mul a a) (mul a b)) (neg (mul a a)))
            (add (add (mul a b) (mul b b)) (neg (mul b b)))) := by
      exact BEDC.Derived.AbGroupUp.abgroup_mul_middle_four addAssoc addComm addCongr
        (add (mul a a) (mul a b)) (add (mul a b) (mul b b))
        (neg (mul a a)) (neg (mul b b))
    have collapse :
        hsame
          (add
            (add (add (mul a a) (mul a b)) (neg (mul a a)))
            (add (add (mul a b) (mul b b)) (neg (mul b b))))
          (add (mul a b) (mul a b)) := by
      exact addCongr (collapseHead (mul a a) (mul a b))
        (collapseTail (mul b b) (mul a b))
    exact hsame_trans expanded (hsame_trans regroup collapse)
  have signed :
      hsame
        (add (mul (add a (neg b)) (add a (neg b)))
          (add (neg (mul a a)) (neg (mul b b))))
        (add (neg (mul a b)) (neg (mul a b))) := by
    have expanded :
        hsame
          (add (mul (add a (neg b)) (add a (neg b)))
            (add (neg (mul a a)) (neg (mul b b))))
          (add
            (add (add (mul a a) (neg (mul a b)))
              (add (neg (mul a b)) (mul b b)))
            (add (neg (mul a a)) (neg (mul b b)))) := by
      exact addCongr
        (commring_square_signed_difference_expand addAssoc addComm zeroLeft negLeft
          addCongr mulComm mulCongr leftDistrib rightDistrib)
        (hsame_refl (add (neg (mul a a)) (neg (mul b b))))
    have regroup :
        hsame
          (add
            (add (add (mul a a) (neg (mul a b)))
              (add (neg (mul a b)) (mul b b)))
            (add (neg (mul a a)) (neg (mul b b))))
          (add
            (add (add (mul a a) (neg (mul a b))) (neg (mul a a)))
            (add (add (neg (mul a b)) (mul b b)) (neg (mul b b)))) := by
      exact BEDC.Derived.AbGroupUp.abgroup_mul_middle_four addAssoc addComm addCongr
        (add (mul a a) (neg (mul a b))) (add (neg (mul a b)) (mul b b))
        (neg (mul a a)) (neg (mul b b))
    have collapse :
        hsame
          (add
            (add (add (mul a a) (neg (mul a b))) (neg (mul a a)))
            (add (add (neg (mul a b)) (mul b b)) (neg (mul b b))))
          (add (neg (mul a b)) (neg (mul a b))) := by
      exact addCongr (collapseHead (mul a a) (neg (mul a b)))
        (collapseTail (mul b b) (neg (mul a b)))
    exact hsame_trans expanded (hsame_trans regroup collapse)
  exact And.intro positive signed

end BEDC.Derived.CommRingUp
