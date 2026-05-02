import BEDC.Derived.FieldUp.Affine
import BEDC.Derived.FieldUp.SignedFactor

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_square_certified_two_sided_affine_exact
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addRightId : forall x : BHist, hsame (add x BHist.Empty) x)
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (negRight : forall x : BHist, hsame (add x (neg x)) BHist.Empty)
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulLeftId : forall x : BHist, hsame (mul one x) x)
    (mulRightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (mulLeftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (mulRightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    {a b c d x y : BHist}
    (alphaA : (hsame a BHist.Empty -> False) -> NonZero a)
    (alphaB : (hsame b BHist.Empty -> False) -> NonZero b)
    (pa2 : NonZero (mul a a)) (pb2 : NonZero (mul b b)) :
    let pa := alphaA ((field_product_nonzero_excludes_zero_factors addAssoc zeroLeft
      negLeft addCongr mulCongr leftDistrib rightDistrib nonzeroTransport
      nonzeroEmptyAbsurd pa2).left)
    let pb := alphaB ((field_product_nonzero_excludes_zero_factors addAssoc zeroLeft
      negLeft addCongr mulCongr leftDistrib rightDistrib nonzeroTransport
      nonzeroEmptyAbsurd pb2).left)
    (hsame (add (mul (mul a x) b) d) c ↔
      hsame x (mul (inv a pa) (mul (add c (neg d)) (inv b pb)))) ∧
      (hsame (add (mul (mul a x) b) d) (add (mul (mul a y) b) d) ↔ hsame x y) := by
  have apartA :=
    (field_product_nonzero_excludes_zero_factors addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib nonzeroTransport nonzeroEmptyAbsurd
      (a := a) (b := a) pa2).left
  have apartB :=
    (field_product_nonzero_excludes_zero_factors addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib nonzeroTransport nonzeroEmptyAbsurd
      (a := b) (b := b) pb2).left
  constructor
  · exact
      field_affine_two_sided_equation_exact_from_apartness addAssoc addRightId
        addCongr negLeft negRight mulAssoc mulLeftId mulRightId mulCongr
        mulLeftInv mulRightInv (a := a) (b := b) (x := x) (d := d) (c := c)
        (alphaA apartA) (alphaB apartB)
  · exact
      field_affine_two_sided_map_classifier_exact_from_apartness addAssoc
        addRightId addCongr negRight mulAssoc mulLeftId mulRightId mulCongr
        mulLeftInv mulRightInv (a := a) (b := b) (x := x) (y := y) (d := d)
        (alphaA apartA) (alphaB apartB)

theorem field_square_certified_affine_solution_unique
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addRightId : forall x : BHist, hsame (add x BHist.Empty) x)
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (negRight : forall x : BHist, hsame (add x (neg x)) BHist.Empty)
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulLeftId : forall x : BHist, hsame (mul one x) x)
    (mulRightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (mulLeftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (mulRightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    {a b c d x y : BHist}
    (alphaA : (hsame a BHist.Empty -> False) -> NonZero a)
    (alphaB : (hsame b BHist.Empty -> False) -> NonZero b)
    (pa2 : NonZero (mul a a)) (pb2 : NonZero (mul b b)) :
    hsame (add (mul (mul a x) b) d) c ->
      hsame (add (mul (mul a y) b) d) c -> hsame x y := by
  intro solutionX solutionY
  have exactness :=
    field_square_certified_two_sided_affine_exact addAssoc addRightId zeroLeft addCongr
      negLeft negRight mulAssoc mulLeftId mulRightId mulCongr leftDistrib rightDistrib
      mulLeftInv mulRightInv nonzeroTransport nonzeroEmptyAbsurd (a := a) (b := b)
      (c := c) (d := d) (x := x) (y := y) alphaA alphaB pa2 pb2
  exact exactness.right.mp (hsame_trans solutionX (hsame_symm solutionY))

end BEDC.Derived.FieldUp
