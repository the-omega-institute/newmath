import BEDC.Derived.FieldUp.Affine

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

protected theorem field_left_mul_empty_equation_solution_unique_from_apartness
    {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    {a x y : BHist} (pa : NonZero a) :
    hsame (mul a x) BHist.Empty ->
      hsame (mul a y) BHist.Empty -> hsame x y := by
  intro hx hy
  have sx : hsame x (mul (inv a pa) BHist.Empty) := by
    have cancelX :
        hsame (mul (inv a pa) (mul a x)) x :=
      field_mul_inverse_left_cancel_from_apartness assocC leftId mulCongr leftInv a x pa
    have transportX :
        hsame (mul (inv a pa) (mul a x)) (mul (inv a pa) BHist.Empty) :=
      mulCongr (hsame_refl (inv a pa)) hx
    exact hsame_trans (hsame_symm cancelX) transportX
  have sy : hsame y (mul (inv a pa) BHist.Empty) := by
    have cancelY :
        hsame (mul (inv a pa) (mul a y)) y :=
      field_mul_inverse_left_cancel_from_apartness assocC leftId mulCongr leftInv a y pa
    have transportY :
        hsame (mul (inv a pa) (mul a y)) (mul (inv a pa) BHist.Empty) :=
      mulCongr (hsame_refl (inv a pa)) hy
    exact hsame_trans (hsame_symm cancelY) transportY
  exact hsame_trans sx (hsame_symm sy)

protected theorem field_affine_left_equation_solution_unique_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addRightId : forall x : BHist, hsame (add x BHist.Empty) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (negRight : forall x : BHist, hsame (add x (neg x)) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a x y d c : BHist} (pa : NonZero a) :
    hsame (add (mul a x) d) c ->
      hsame (add (mul a y) d) c -> hsame x y := by
  intro hx hy
  have sameAffine :
      hsame (add (mul a x) d) (add (mul a y) d) :=
    hsame_trans hx (hsame_symm hy)
  exact
    ((field_affine_one_sided_map_classifier_exact_from_apartness
      addAssoc addRightId addCongr negRight assocC leftId rightId mulCongr
      leftInv rightInv (a := a) (b := a) (u := d) (v := d) pa pa).1).mp
      sameAffine

end BEDC.Derived.FieldUp
