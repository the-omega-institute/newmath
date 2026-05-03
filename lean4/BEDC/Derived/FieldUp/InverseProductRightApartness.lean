import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_inverse_product_reverse_right_inverse_apart_empty_from_one_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (oneApartEmpty : hsame one BHist.Empty -> False)
    {a b : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a b) (mul (inv b pb) (inv a pa))) BHist.Empty -> False := by
  intro productEmpty
  have inner :
      hsame (mul b (mul (inv b pb) (inv a pa))) (inv a pa) := by
    exact hsame_trans (hsame_symm (assocC b (inv b pb) (inv a pa)))
      (hsame_trans (mulCongr (rightInv b pb) (hsame_refl (inv a pa)))
        (leftId (inv a pa)))
  have productOne :
      hsame (mul (mul a b) (mul (inv b pb) (inv a pa))) one := by
    exact hsame_trans (assocC a b (mul (inv b pb) (inv a pa)))
      (hsame_trans (mulCongr (hsame_refl a) inner) (rightInv a pa))
  exact oneApartEmpty (hsame_trans (hsame_symm productOne) productEmpty)

end BEDC.Derived.FieldUp
