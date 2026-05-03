import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem commring_empty_linear_factor_equal_squares {add mul : BHist -> BHist -> BHist}
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
    hsame (add a b) BHist.Empty ∨ hsame (add a (neg b)) BHist.Empty ->
      hsame (mul a a) (mul b b) := by
  intro emptyFactor
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have zeroProducts :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  have productZero : hsame (mul (add a b) (add a (neg b))) BHist.Empty := by
    cases emptyFactor with
    | inl leftEmpty =>
        exact hsame_trans
          (mulCongr leftEmpty (hsame_refl (add a (neg b))))
          (zeroProducts.right (add a (neg b)))
    | inr rightEmpty =>
        exact hsame_trans
          (mulCongr (hsame_refl (add a b)) rightEmpty)
          (zeroProducts.left (add a b))
  exact (commring_difference_of_squares_zero_exact addAssoc addComm zeroLeft negLeft
    addCongr mulCongr leftDistrib mulComm a b).mp productZero

end BEDC.Derived.CommRingUp
