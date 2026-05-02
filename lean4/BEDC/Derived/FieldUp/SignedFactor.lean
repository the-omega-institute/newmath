import BEDC.Derived.FieldUp
import BEDC.Derived.CommRingUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_product_nonzero_excludes_zero_factors {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {NonZero : BHist -> Prop}
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
    {a b : BHist} (pab : NonZero (mul a b)) :
    (hsame a BHist.Empty -> False) ∧ (hsame b BHist.Empty -> False) := by
  have zeroAbsorption :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  constructor
  · intro aEmpty
    have productEmpty : hsame (mul a b) BHist.Empty := by
      exact hsame_trans (mulCongr aEmpty (hsame_refl b)) (zeroAbsorption.right b)
    exact nonzeroEmptyAbsurd (nonzeroTransport productEmpty pab)
  · intro bEmpty
    have productEmpty : hsame (mul a b) BHist.Empty := by
      exact hsame_trans (mulCongr (hsame_refl a) bEmpty) (zeroAbsorption.left a)
    exact nonzeroEmptyAbsurd (nonzeroTransport productEmpty pab)

theorem field_equal_squares_signed_factor_exclusion {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (sameSquares : hsame (mul a a) (mul b b)) :
    (NonZero (add a b) -> hsame (add a (neg b)) BHist.Empty) ∧
      (NonZero (add a (neg b)) -> hsame (add a b) BHist.Empty) := by
  have signedProductZero : hsame (mul (add a b) (add a (neg b))) BHist.Empty := by
    exact BEDC.Derived.CommRingUp.commring_equal_squares_signed_factor_zero addAssoc
      addComm zeroLeft negLeft addCongr mulComm mulCongr leftDistrib sameSquares
  have cancel :=
    field_one_sided_zero_product_cancel_from_apartness addAssoc zeroLeft negLeft assocC
      leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
      (add a b) (add a (neg b))
  constructor
  · intro nonzeroPlus
    exact cancel.left nonzeroPlus signedProductZero
  · intro nonzeroMinus
    exact cancel.right nonzeroMinus signedProductZero

theorem field_equal_squares_signed_factor_endpoint_collapse
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (addRightId : forall x : BHist, hsame (add x BHist.Empty) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (negRight : forall x : BHist, hsame (add x (neg x)) BHist.Empty)
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
    {a b : BHist} :
    hsame (mul a a) (mul b b) ->
      (NonZero (add a b) -> hsame a b) ∧
        (NonZero (add a (neg b)) -> hsame a (neg b)) := by
  intro sameSquares
  have endpoints :=
    field_equal_squares_signed_factor_exclusion addAssoc addComm zeroLeft negLeft assocC
      leftId rightId addCongr mulComm mulCongr leftDistrib rightDistrib leftInv rightInv
      sameSquares
  constructor
  · intro nonzeroPlus
    exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
      addAssoc zeroLeft addRightId addCongr
      (endpoints.left nonzeroPlus)
      (negLeft b)
  · intro nonzeroMinus
    exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
      addAssoc zeroLeft addRightId addCongr
      (endpoints.right nonzeroMinus)
      (negRight b)

end BEDC.Derived.FieldUp
