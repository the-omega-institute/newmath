import BEDC.FKernel.Hist

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem commring_right_distrib_from_left {add mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z))) :
    forall x y z : BHist, hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
  intro x y z
  exact hsame_trans (mulComm (add x y) z)
    (hsame_trans (leftDistrib z x y)
      (addCongr (mulComm z x) (mulComm z y)))

 theorem commring_left_distrib_from_right {add mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y z : BHist, hsame (mul x (add y z)) (add (mul x y) (mul x z)) := by
  intro x y z
  exact hsame_trans (mulComm x (add y z))
    (hsame_trans (rightDistrib y z x)
      (addCongr (mulComm y x) (mulComm z x)))

theorem commring_square_add_expand {add mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall a b : BHist,
      hsame (mul (add a b) (add a b))
        (add (add (mul a a) (mul a b)) (add (mul a b) (mul b b))) := by
  intro a b
  have outer :
      hsame (mul (add a b) (add a b))
        (add (mul a (add a b)) (mul b (add a b))) := by
    exact rightDistrib a b (add a b)
  have expandLeft :
      hsame (add (mul a (add a b)) (mul b (add a b)))
        (add (add (mul a a) (mul a b)) (add (mul b a) (mul b b))) := by
    exact addCongr (leftDistrib a a b) (leftDistrib b a b)
  have alignMiddle :
      hsame (add (add (mul a a) (mul a b)) (add (mul b a) (mul b b)))
        (add (add (mul a a) (mul a b)) (add (mul a b) (mul b b))) := by
    exact addCongr (hsame_refl (add (mul a a) (mul a b)))
      (addCongr (mulComm b a) (hsame_refl (mul b b)))
  exact hsame_trans outer (hsame_trans expandLeft alignMiddle)

end BEDC.Derived.CommRingUp
