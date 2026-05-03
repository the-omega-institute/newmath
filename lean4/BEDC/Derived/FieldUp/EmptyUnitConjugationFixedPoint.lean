import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_empty_unit_conjugation_fixed_point_commutation_iff
    {mul : BHist -> BHist -> BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) BHist.Empty)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) BHist.Empty)
    {a b : BHist} (pa : NonZero a) :
    hsame (mul (mul a b) (inv a pa)) b <-> hsame (mul a b) (mul b a) := by
  constructor
  · intro fixed
    have transported :
        hsame (mul (mul (mul a b) (inv a pa)) a) (mul b a) := by
      exact mulCongr fixed (hsame_refl a)
    have collapse :
        hsame (mul (mul (mul a b) (inv a pa)) a) (mul a b) := by
      exact hsame_trans (assocC (mul a b) (inv a pa) a)
        (hsame_trans (mulCongr (hsame_refl (mul a b)) (leftInv a pa))
          (rightId (mul a b)))
    exact hsame_trans (hsame_symm collapse) transported
  · intro commute
    have transported :
        hsame (mul (mul a b) (inv a pa)) (mul (mul b a) (inv a pa)) := by
      exact mulCongr commute (hsame_refl (inv a pa))
    have collapse : hsame (mul (mul b a) (inv a pa)) b := by
      exact hsame_trans (assocC b a (inv a pa))
        (hsame_trans (mulCongr (hsame_refl b) (rightInv a pa)) (rightId b))
    exact hsame_trans transported collapse

end BEDC.Derived.FieldUp
