import BEDC.Derived.FieldUp
import BEDC.Derived.FieldUp.SignedFactor

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_square_apartness_inverse_descent
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {inv : (a : BHist) -> (hsame a BHist.Empty -> False) -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul a (inv a p)) one)
    {a : BHist} (pSquare : hsame (mul a a) BHist.Empty -> False) :
    Exists (fun pa : hsame a BHist.Empty -> False =>
      hsame (inv (mul a a) pSquare) (mul (inv a pa) (inv a pa))) := by
  have zeroAbsorption :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  let pa : hsame a BHist.Empty -> False := by
    intro sameEmpty
    have productToZeroLeft : hsame (mul a a) (mul BHist.Empty a) := by
      exact mulCongr sameEmpty (hsame_refl a)
    exact pSquare (hsame_trans productToZeroLeft (zeroAbsorption.right a))
  exact Exists.intro pa
    (field_inverse_product_reverse_from_apartness assocC leftId rightId mulCongr leftInv
      rightInv pSquare pa pa)

theorem field_square_zero_rejects_factor_nonzero
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    {a : BHist} :
    hsame (mul a a) BHist.Empty ->
      (NonZero a -> False) ∧ ((hsame (mul a a) BHist.Empty -> False) -> False) := by
  intro squareZero
  have cancel :=
    field_one_sided_zero_product_cancel_from_apartness addAssoc zeroLeft negLeft
      assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv a a
  constructor
  · intro nonzeroA
    have factorEmpty : hsame a BHist.Empty := cancel.left nonzeroA squareZero
    exact nonzeroEmptyAbsurd (nonzeroTransport factorEmpty nonzeroA)
  · intro squareApart
    exact squareApart squareZero

theorem field_square_nonzero_one_sided_mul_exact
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    (apartToNonzero : forall {h : BHist}, (hsame h BHist.Empty -> False) -> NonZero h)
    {a c x : BHist} (pSquare : NonZero (mul a a)) :
    let pa := apartToNonzero (field_product_nonzero_excludes_zero_factors addAssoc
      zeroLeft negLeft addCongr mulCongr leftDistrib rightDistrib nonzeroTransport
      nonzeroEmptyAbsurd (a := a) (b := a) pSquare).left
    (hsame (mul a x) c ↔ hsame x (mul (inv a pa) c)) ∧
      (hsame (mul x a) c ↔ hsame x (mul c (inv a pa))) := by
  let pa := apartToNonzero (field_product_nonzero_excludes_zero_factors addAssoc
    zeroLeft negLeft addCongr mulCongr leftDistrib rightDistrib nonzeroTransport
    nonzeroEmptyAbsurd (a := a) (b := a) pSquare).left
  constructor
  · exact field_left_mul_equation_exact_from_apartness
      assocC leftId mulCongr leftInv rightInv pa
  · exact field_right_mul_equation_exact_from_apartness
      assocC rightId mulCongr leftInv rightInv pa

theorem field_square_nonzero_two_sided_mul_exact
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    (apartToNonzero : forall {h : BHist}, (hsame h BHist.Empty -> False) -> NonZero h)
    {a c x : BHist} (pSquare : NonZero (mul a a)) :
    let pa := apartToNonzero (field_product_nonzero_excludes_zero_factors addAssoc
      zeroLeft negLeft addCongr mulCongr leftDistrib rightDistrib nonzeroTransport
      nonzeroEmptyAbsurd (a := a) (b := a) pSquare).left
    hsame (mul (mul a x) a) c <->
      hsame x (mul (inv a pa) (mul c (inv a pa))) := by
  let pa := apartToNonzero (field_product_nonzero_excludes_zero_factors addAssoc
    zeroLeft negLeft addCongr mulCongr leftDistrib rightDistrib nonzeroTransport
    nonzeroEmptyAbsurd (a := a) (b := a) pSquare).left
  exact field_middle_mul_equation_exact_from_apartness
    assocC leftId rightId mulCongr leftInv rightInv pa pa

end BEDC.Derived.FieldUp
