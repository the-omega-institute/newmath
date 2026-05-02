import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_right_mul_empty_equation_solution_unique_from_apartness
    {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {x y b : BHist} (pb : NonZero b) :
    hsame (mul x b) BHist.Empty -> hsame (mul y b) BHist.Empty -> hsame x y := by
  intro hx hy
  have sx : hsame x (mul BHist.Empty (inv b pb)) :=
    field_right_mul_equation_solution_from_apartness assocC rightId mulCongr rightInv pb hx
  have sy : hsame y (mul BHist.Empty (inv b pb)) :=
    field_right_mul_equation_solution_from_apartness assocC rightId mulCongr rightInv pb hy
  exact hsame_trans sx (hsame_symm sy)

protected theorem field_middle_mul_empty_equation_solution_unique_from_apartness
    {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a x y b : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a x) b) BHist.Empty ->
      hsame (mul (mul a y) b) BHist.Empty -> hsame x y := by
  intro hx hy
  have sx : hsame x (mul (inv a pa) (mul BHist.Empty (inv b pb))) :=
    field_middle_mul_equation_solution_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pa pb hx
  have sy : hsame y (mul (inv a pa) (mul BHist.Empty (inv b pb))) :=
    field_middle_mul_equation_solution_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pa pb hy
  exact hsame_trans sx (hsame_symm sy)

end BEDC.Derived.FieldUp
