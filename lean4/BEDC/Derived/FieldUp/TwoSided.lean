import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_two_sided_product_nonzero_excludes_middle_zero
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
    {a b x : BHist} (pa : NonZero a) (pb : NonZero b) :
    NonZero (mul (mul a x) b) -> hsame x BHist.Empty -> False := by
  intro productNonzero xEmpty
  have productEmpty : hsame (mul (mul a x) b) BHist.Empty := by
    exact Iff.mpr
      (field_two_sided_empty_product_exact_from_apartness addAssoc zeroLeft negLeft
        assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
        pa pb)
      xEmpty
  exact nonzeroEmptyAbsurd (nonzeroTransport productEmpty productNonzero)

 theorem field_two_sided_product_apartzero_exact_from_apartness
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
    {a b x : BHist} (pa : NonZero a) (pb : NonZero b) :
    ((hsame (mul (mul a x) b) BHist.Empty -> False) <->
      (hsame x BHist.Empty -> False)) := by
  have emptyExact :
      hsame (mul (mul a x) b) BHist.Empty <-> hsame x BHist.Empty :=
    field_two_sided_empty_product_exact_from_apartness addAssoc zeroLeft negLeft
      assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
      pa pb
  constructor
  · intro productApart xEmpty
    exact productApart (Iff.mpr emptyExact xEmpty)
  · intro xApart productEmpty
    exact xApart (Iff.mp emptyExact productEmpty)

 theorem field_affine_two_sided_empty_zero_map_classifier_exact_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
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
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x y d : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (add (mul (mul a x) b) d) (add (mul (mul a y) b) d) <-> hsame x y := by
  have addRightId : forall x : BHist, hsame (add x BHist.Empty) x := by
    exact BEDC.Derived.RingUp.ring_add_right_zero addComm zeroLeft
  have addRightInv : forall x : BHist, hsame (add x (neg x)) BHist.Empty := by
    exact BEDC.Derived.RingUp.ring_add_right_inverse addComm negLeft
  constructor
  · intro affineSame
    have productsSame : hsame (mul (mul a x) b) (mul (mul a y) b) := by
      exact BEDC.Derived.GroupUp.group_right_cancel
        (mul := add) (e := BHist.Empty) (inv := neg)
        addAssoc addRightId addCongr addRightInv affineSame
    exact Iff.mp
      (field_two_sided_mul_exact_from_apartness assocC leftId rightId mulCongr leftInv
        rightInv pa pb)
      productsSame
  · intro middleSame
    have productsSame : hsame (mul (mul a x) b) (mul (mul a y) b) := by
      exact mulCongr (mulCongr (hsame_refl a) middleSame) (hsame_refl b)
    exact addCongr productsSame (hsame_refl d)

end BEDC.Derived.FieldUp
