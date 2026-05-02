import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

 theorem field_affine_left_equation_exact_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a x d c : BHist} (pa : NonZero a) :
    hsame (add (mul a x) d) c <-> hsame x (mul (inv a pa) (add c (neg d))) := by
  have addRightId : forall y : BHist, hsame (add y BHist.Empty) y := by
    intro y
    exact hsame_trans (addComm y BHist.Empty) (zeroLeft y)
  have addRightInv : forall y : BHist, hsame (add y (neg y)) BHist.Empty := by
    intro y
    exact hsame_trans (addComm y (neg y)) (negLeft y)
  constructor
  · intro sameAffine
    have sameLinear : hsame (mul a x) (add c (neg d)) := by
      exact BEDC.Derived.GroupUp.group_right_mul_equation_solution
        addAssoc addRightId addCongr addRightInv sameAffine
    exact Iff.mp
      (field_left_mul_equation_exact_from_apartness
        assocC leftId mulCongr leftInv rightInv pa)
      sameLinear
  · intro sameSolution
    have sameLinear : hsame (mul a x) (add c (neg d)) := by
      exact Iff.mpr
        (field_left_mul_equation_exact_from_apartness
          assocC leftId mulCongr leftInv rightInv pa)
        sameSolution
    have transported :
        hsame (add (mul a x) d) (add (add c (neg d)) d) := by
      exact addCongr sameLinear (hsame_refl d)
    have collapseOffset : hsame (add (add c (neg d)) d) c := by
      exact hsame_trans (addAssoc c (neg d) d)
        (hsame_trans (addCongr (hsame_refl c) (negLeft d)) (addRightId c))
    exact hsame_trans transported collapseOffset

 theorem field_affine_right_equation_exact_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {x b d c : BHist} (pb : NonZero b) :
    hsame (add (mul x b) d) c <-> hsame x (mul (add c (neg d)) (inv b pb)) := by
  have addRightId : forall y : BHist, hsame (add y BHist.Empty) y := by
    intro y
    exact hsame_trans (addComm y BHist.Empty) (zeroLeft y)
  have addRightInv : forall y : BHist, hsame (add y (neg y)) BHist.Empty := by
    intro y
    exact hsame_trans (addComm y (neg y)) (negLeft y)
  constructor
  · intro sameAffine
    have sameLinear : hsame (mul x b) (add c (neg d)) := by
      exact BEDC.Derived.GroupUp.group_right_mul_equation_solution
        addAssoc addRightId addCongr addRightInv sameAffine
    exact Iff.mp
      (field_right_mul_equation_exact_from_apartness
        assocC rightId mulCongr leftInv rightInv pb)
      sameLinear
  · intro sameSolution
    have sameLinear : hsame (mul x b) (add c (neg d)) := by
      exact Iff.mpr
        (field_right_mul_equation_exact_from_apartness
          assocC rightId mulCongr leftInv rightInv pb)
        sameSolution
    have transported :
        hsame (add (mul x b) d) (add (add c (neg d)) d) := by
      exact addCongr sameLinear (hsame_refl d)
    have collapseOffset : hsame (add (add c (neg d)) d) c := by
      exact hsame_trans (addAssoc c (neg d) d)
        (hsame_trans (addCongr (hsame_refl c) (negLeft d)) (addRightId c))
    exact hsame_trans transported collapseOffset

end BEDC.Derived.FieldUp
