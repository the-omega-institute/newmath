import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_empty_unit_right_mul_cancel_from_apartness
    {mul : BHist -> BHist -> BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall (a : BHist) (p : NonZero a),
      hsame (mul a (inv a p)) BHist.Empty)
    {x y b : BHist} (pb : NonZero b) :
    hsame (mul x b) (mul y b) -> hsame x y := by
  intro sameProduct
  have solvedX : hsame x (mul (mul y b) (inv b pb)) := by
    exact field_right_mul_equation_solution_from_apartness
      assocC rightId mulCongr rightInv pb sameProduct
  have collapseY : hsame (mul (mul y b) (inv b pb)) y := by
    exact field_mul_inverse_right_cancel_from_apartness
      assocC rightId mulCongr rightInv y b pb
  exact hsame_trans solvedX collapseY

protected theorem field_empty_unit_left_mul_cancel_from_apartness
    {mul : BHist -> BHist -> BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a),
      hsame (mul (inv a p) a) BHist.Empty)
    {a x y : BHist} (pa : NonZero a) :
    hsame (mul a x) (mul a y) -> hsame x y := by
  intro sameProduct
  have transported :
      hsame (mul (inv a pa) (mul a x)) (mul (inv a pa) (mul a y)) := by
    exact mulCongr (hsame_refl (inv a pa)) sameProduct
  have collapseX : hsame (mul (inv a pa) (mul a x)) x := by
    exact field_mul_inverse_left_cancel_from_apartness
      assocC leftId mulCongr leftInv a x pa
  have collapseY : hsame (mul (inv a pa) (mul a y)) y := by
    exact field_mul_inverse_left_cancel_from_apartness
      assocC leftId mulCongr leftInv a y pa
  exact hsame_trans (hsame_symm collapseX) (hsame_trans transported collapseY)

end BEDC.Derived.FieldUp
