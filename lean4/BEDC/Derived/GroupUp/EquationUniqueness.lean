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

protected theorem group_right_mul_equation_solution_unique_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {x y a b : BHist} :
    hsame (mul x a) b -> hsame (mul y a) b -> hsame x y := by
  intro hx hy
  have sx : hsame x (mul b (inv a)) :=
    group_right_mul_equation_solution assocC rightId mulCongr rightInv hx
  have sy : hsame y (mul b (inv a)) :=
    group_right_mul_equation_solution assocC rightId mulCongr rightInv hy
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

protected theorem group_two_sided_mul_equation_exact_from_empty_unit_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x b c : BHist} :
    hsame (mul (mul a x) c) b <->
      hsame x (mul (inv a) (mul b (inv c))) := by
  constructor
  · intro twoSided
    have solveRight : hsame (mul a x) (mul b (inv c)) :=
      (group_right_mul_equation_exact_from_empty_unit assocC rightId mulCongr
        leftInv rightInv).mp twoSided
    exact (group_left_mul_equation_exact_from_empty_unit assocC leftId mulCongr
      leftInv rightInv).mp solveRight
  · intro solved
    have solveLeft : hsame (mul a x) (mul b (inv c)) :=
      (group_left_mul_equation_exact_from_empty_unit assocC leftId mulCongr
        leftInv rightInv).mpr solved
    exact (group_right_mul_equation_exact_from_empty_unit assocC rightId mulCongr
      leftInv rightInv).mpr solveLeft

end BEDC.Derived.GroupUp
