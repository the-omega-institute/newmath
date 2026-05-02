import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_square_apartness_inverse_descent
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {inv : (a : BHist) -> (hsame a BHist.Empty -> False) -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul a (inv a p)) one)
    {a : BHist} (pSquare : hsame (mul a a) BHist.Empty -> False) :
    Exists (fun pa : hsame a BHist.Empty -> False =>
      hsame (inv (mul a a) pSquare) (mul (inv a pa) (inv a pa))) := by
  have zeroAbsorption :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  let pa : hsame a BHist.Empty -> False := by
    intro sameEmpty
    have productToZeroLeft : hsame (mul a a) (mul BHist.Empty a) := by
      exact mulCongr sameEmpty (hsame_refl a)
    exact pSquare (hsame_trans productToZeroLeft (zeroAbsorption.right a))
  exact Exists.intro pa
    (field_inverse_product_reverse_from_apartness assocC leftId rightId mulCongr leftInv
      rightInv pSquare pa pa)

end BEDC.Derived.FieldUp
