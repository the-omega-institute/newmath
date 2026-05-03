import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_left_mul_equation_solution_unique_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    {a x y b : BHist} :
    hsame (mul a x) b -> hsame (mul a y) b -> hsame x y := by
  intro hx hy
  have sx : hsame x (mul (inv a) b) :=
    group_left_mul_equation_solution assocC leftId mulCongr leftInv hx
  have sy : hsame y (mul (inv a) b) :=
    group_left_mul_equation_solution assocC leftId mulCongr leftInv hy
  exact hsame_trans sx (hsame_symm sy)

protected theorem group_conjugation_equation_solution_unique_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y b : BHist} :
    hsame (mul (mul a x) (inv a)) b ->
      hsame (mul (mul a y) (inv a)) b -> hsame x y := by
  intro hx hy
  have sx : hsame x (mul (mul (inv a) b) a) :=
    (group_conjugation_equation_exact_from_empty_unit_iff assocC leftId rightId mulCongr
      leftInv rightInv).mp hx
  have sy : hsame y (mul (mul (inv a) b) a) :=
    (group_conjugation_equation_exact_from_empty_unit_iff assocC leftId rightId mulCongr
      leftInv rightInv).mp hy
  exact hsame_trans sx (hsame_symm sy)

end BEDC.Derived.GroupUp
