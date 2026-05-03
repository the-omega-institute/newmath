import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

theorem group_product_unit_inverse_correspondence {mul : BHist -> BHist -> BHist}
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
  constructor
  · constructor
    · intro productUnit
      have solved :
          hsame a (mul BHist.Empty (inv b)) :=
        Iff.mp
          (group_right_mul_equation_exact_from_empty_unit
            assocC rightId mulCongr leftInv rightInv)
          productUnit
      exact hsame_trans solved (leftId (inv b))
    · intro endpoint
      have solved : hsame a (mul BHist.Empty (inv b)) :=
        hsame_trans endpoint (hsame_symm (leftId (inv b)))
      exact Iff.mpr
        (group_right_mul_equation_exact_from_empty_unit
          assocC rightId mulCongr leftInv rightInv)
        solved
  · constructor
    · intro productUnit
      have solved :
          hsame b (mul (inv a) BHist.Empty) :=
        Iff.mp
          (group_left_mul_equation_exact_from_empty_unit
            assocC leftId mulCongr leftInv rightInv)
          productUnit
      exact hsame_trans solved (rightId (inv a))
    · intro endpoint
      have solved : hsame b (mul (inv a) BHist.Empty) :=
        hsame_trans endpoint (hsame_symm (rightId (inv a)))
      exact Iff.mpr
        (group_left_mul_equation_exact_from_empty_unit
          assocC leftId mulCongr leftInv rightInv)
        solved

end BEDC.Derived.GroupUp
