import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_inverse_apart_empty_from_one_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (zeroLeft : forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty)
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (oneApartEmpty : hsame one BHist.Empty -> False)
    {a : BHist} (pa : NonZero a) :
    hsame (inv a pa) BHist.Empty -> False := by
  intro inverseEmpty
  have productEmpty : hsame (mul (inv a pa) a) BHist.Empty := by
    exact hsame_trans (mulCongr inverseEmpty (hsame_refl a)) (zeroLeft a)
  exact oneApartEmpty (hsame_trans (hsame_symm (leftInv a pa)) productEmpty)

protected theorem field_inverse_apart_empty_from_right_inverse_one_apartness
    {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (zeroRight : forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (oneApartEmpty : hsame one BHist.Empty -> False)
    {a : BHist} (pa : NonZero a) :
    hsame (inv a pa) BHist.Empty -> False := by
  intro inverseEmpty
  have productEmpty : hsame (mul a (inv a pa)) BHist.Empty := by
    exact hsame_trans (mulCongr (hsame_refl a) inverseEmpty) (zeroRight a)
  exact oneApartEmpty (hsame_trans (hsame_symm (rightInv a pa)) productEmpty)

protected theorem field_inverse_nonzero_from_right_inverse_one_apartness
    {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (zeroRight : forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (oneApartEmpty : hsame one BHist.Empty -> False)
    (nonzeroOfApartEmpty : forall x : BHist, (hsame x BHist.Empty -> False) -> NonZero x)
    {a : BHist} (pa : NonZero a) :
    NonZero (inv a pa) := by
  exact nonzeroOfApartEmpty (inv a pa)
    (BEDC.Derived.FieldUp.field_inverse_apart_empty_from_right_inverse_one_apartness
      mulCongr zeroRight rightInv oneApartEmpty pa)

end BEDC.Derived.FieldUp
