import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

theorem group_product_unit_inverse_correspondence_iff {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b : BHist} :
    (hsame (mul a b) BHist.Empty <-> hsame a (inv b)) ∧
      (hsame (mul a b) BHist.Empty <-> hsame b (inv a)) := by
  have rightExact :
      hsame (mul a b) BHist.Empty <-> hsame a (mul BHist.Empty (inv b)) := by
    exact group_right_mul_equation_exact_from_empty_unit assocC rightId mulCongr
      leftInv rightInv
  have leftExact :
      hsame (mul a b) BHist.Empty <-> hsame b (mul (inv a) BHist.Empty) := by
    exact group_left_mul_equation_exact_from_empty_unit assocC leftId mulCongr
      leftInv rightInv
  constructor
  · constructor
    · intro productUnit
      exact hsame_trans (rightExact.mp productUnit) (leftId (inv b))
    · intro sameInverse
      exact rightExact.mpr (hsame_trans sameInverse (hsame_symm (leftId (inv b))))
  · constructor
    · intro productUnit
      exact hsame_trans (leftExact.mp productUnit) (rightId (inv a))
    · intro sameInverse
      exact leftExact.mpr (hsame_trans sameInverse (hsame_symm (rightId (inv a))))

end BEDC.Derived.GroupUp
