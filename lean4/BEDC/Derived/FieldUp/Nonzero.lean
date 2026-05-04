import BEDC.Derived.FieldUp
import BEDC.Derived.CommRingUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_product_nonzero_empty_factors_absurd
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {NonZero : BHist -> Prop}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    {a b : BHist} :
    NonZero (mul a b) -> (hsame a BHist.Empty -> False) ∧
      (hsame b BHist.Empty -> False) := by
  intro productNonzero
  have zeroAbsorption :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft
      addCongr mulCongr leftDistrib rightDistrib
  constructor
  · intro aEmpty
    have productEmpty : hsame (mul a b) BHist.Empty := by
      exact hsame_trans (mulCongr aEmpty (hsame_refl b)) (zeroAbsorption.right b)
    exact nonzeroEmptyAbsurd (nonzeroTransport productEmpty productNonzero)
  · intro bEmpty
    have productEmpty : hsame (mul a b) BHist.Empty := by
      exact hsame_trans (mulCongr (hsame_refl a) bEmpty) (zeroAbsorption.left a)
    exact nonzeroEmptyAbsurd (nonzeroTransport productEmpty productNonzero)

theorem field_product_nonzero_of_nonzero_factors
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
    {a b : BHist} (pa : NonZero a) (pb : NonZero b) :
    NonZero (mul a b) := by
  exact apartToNonzero
    (field_nonzero_factors_exclude_empty_product addAssoc zeroLeft negLeft assocC
      leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
      nonzeroTransport nonzeroEmptyAbsurd pa pb)

theorem field_binary_product_nonzero_iff_factors
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
    {a b : BHist} :
    NonZero (mul a b) <-> NonZero a ∧ NonZero b := by
  constructor
  · intro productNonzero
    have apartFactors :
        (hsame a BHist.Empty -> False) ∧ (hsame b BHist.Empty -> False) :=
      field_product_nonzero_empty_factors_absurd addAssoc zeroLeft negLeft addCongr
        mulCongr leftDistrib rightDistrib nonzeroTransport nonzeroEmptyAbsurd productNonzero
    constructor
    · exact apartToNonzero apartFactors.left
    · exact apartToNonzero apartFactors.right
  · intro factors
    exact field_product_nonzero_of_nonzero_factors addAssoc zeroLeft negLeft assocC
      leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
      nonzeroTransport nonzeroEmptyAbsurd apartToNonzero factors.left factors.right

theorem field_equal_squares_signed_factors_not_both_nonzero
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
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
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    {a b : BHist} :
    hsame (mul a a) (mul b b) -> NonZero (add a b) -> NonZero (add a (neg b)) ->
      False := by
  intro sameSquares nonzeroPlus nonzeroMinus
  have signedProductEmpty :
      hsame (mul (add a b) (add a (neg b))) BHist.Empty := by
    exact BEDC.Derived.CommRingUp.commring_equal_squares_signed_factor_zero
      addAssoc addComm zeroLeft negLeft addCongr mulComm mulCongr leftDistrib sameSquares
  exact field_nonzero_factors_exclude_empty_product addAssoc zeroLeft negLeft assocC
    leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
    nonzeroTransport nonzeroEmptyAbsurd nonzeroPlus nonzeroMinus signedProductEmpty

end BEDC.Derived.FieldUp
