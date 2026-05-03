import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

 theorem group_commutator_trivial_iff_commutes_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b : BHist} :
    hsame (mul (mul a b) (mul (inv a) (inv b))) BHist.Empty <->
      hsame (mul a b) (mul b a) := by
  have reverseBA :
      hsame (inv (mul b a)) (mul (inv a) (inv b)) := by
    exact group_inverse_mul_reverse assocC leftId rightId mulCongr leftInv rightInv b a
  constructor
  · intro commUnit
    have reverseLeftInverse :
        hsame (mul (mul (inv a) (inv b)) (mul b a)) BHist.Empty := by
      exact hsame_trans
        (mulCongr (hsame_symm reverseBA) (hsame_refl (mul b a)))
        (leftInv (mul b a))
    exact group_left_right_inverse_uniqueness
      assocC leftId rightId mulCongr commUnit reverseLeftInverse
  · intro commute
    exact hsame_trans
      (mulCongr commute (hsame_symm reverseBA))
      (rightInv (mul b a))

protected theorem group_conjugation_fixed_point_commutation_iff_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b : BHist} :
    hsame (mul (mul a b) (inv a)) b <-> hsame (mul a b) (mul b a) := by
  constructor
  · intro fixed
    have transported :
        hsame (mul (mul (mul a b) (inv a)) a) (mul b a) := by
      exact mulCongr fixed (hsame_refl a)
    have collapse :
        hsame (mul (mul (mul a b) (inv a)) a) (mul a b) := by
      exact hsame_trans (assocC (mul a b) (inv a) a)
        (hsame_trans (mulCongr (hsame_refl (mul a b)) (leftInv a))
          (rightId (mul a b)))
    exact hsame_trans (hsame_symm collapse) transported
  · intro commute
    have transported : hsame (mul (mul a b) (inv a)) (mul (mul b a) (inv a)) := by
      exact mulCongr commute (hsame_refl (inv a))
    have collapse : hsame (mul (mul b a) (inv a)) b := by
      exact hsame_trans (assocC b a (inv a))
        (hsame_trans (mulCongr (hsame_refl b) (rightInv a)) (rightId b))
    exact hsame_trans transported collapse

end BEDC.Derived.GroupUp
