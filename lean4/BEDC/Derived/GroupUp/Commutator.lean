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

end BEDC.Derived.GroupUp
