import BEDC.Derived.CommRingUp.CrossTerm

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem commring_signed_square_zero_diagonal_extraction_package
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
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
    hsame (mul (add a (neg b)) (add a (neg b))) BHist.Empty ->
      hsame (add (mul a a) (mul b b)) (add (mul a b) (mul a b)) ∧
        hsame (add (neg (mul a a)) (neg (mul b b)))
          (add (neg (mul a b)) (neg (mul a b))) := by
  intro squareZero
  have positive :
      hsame (add (mul a a) (mul b b)) (add (mul a b) (mul a b)) :=
    (commring_signed_square_zero_exact addAssoc addComm zeroLeft negLeft addCongr mulComm
      mulCongr leftDistrib).mp squareZero
  have extraction :=
    commring_square_cross_term_extraction_pair addAssoc addComm zeroLeft negLeft addCongr
      mulComm mulCongr leftDistrib (a := a) (b := b)
  have signedCollapse :
      hsame
        (add (mul (add a (neg b)) (add a (neg b)))
          (add (neg (mul a a)) (neg (mul b b))))
        (add (neg (mul a a)) (neg (mul b b))) := by
    exact hsame_trans
      (addCongr squareZero (hsame_refl (add (neg (mul a a)) (neg (mul b b)))))
      (zeroLeft (add (neg (mul a a)) (neg (mul b b))))
  have signed :
      hsame (add (neg (mul a a)) (neg (mul b b)))
        (add (neg (mul a b)) (neg (mul a b))) := by
    exact hsame_trans (hsame_symm signedCollapse) extraction.right
  exact And.intro positive signed

end BEDC.Derived.CommRingUp
