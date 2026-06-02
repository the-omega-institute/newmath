import BEDC.Derived.FieldUp.Nonzero

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

theorem field_two_sided_product_nonzero_middle_factor_iff
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
    {a b x : BHist} (pa : NonZero a) (pb : NonZero b) :
    NonZero (mul (mul a x) b) <-> NonZero x := by
  constructor
  · intro productNonzero
    exact apartToNonzero
      (field_two_sided_product_nonzero_excludes_middle_zero addAssoc zeroLeft negLeft
        assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
        nonzeroTransport nonzeroEmptyAbsurd pa pb productNonzero)
  · intro px
    have nonzeroAX : NonZero (mul a x) :=
      field_product_nonzero_of_nonzero_factors addAssoc zeroLeft negLeft assocC
        leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
        nonzeroTransport nonzeroEmptyAbsurd apartToNonzero pa px
    exact field_product_nonzero_of_nonzero_factors addAssoc zeroLeft negLeft assocC
      leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
      nonzeroTransport nonzeroEmptyAbsurd apartToNonzero nonzeroAX pb

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

theorem field_affine_two_sided_automorphism_composition
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (_addComm : forall x y : BHist, hsame (add x y) (add y x))
    (_zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (_negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (_leftId : forall x : BHist, hsame (mul one x) x)
    (_rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (_leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (_rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b c e d f x : BHist} (_pa : NonZero a) (_pb : NonZero b)
    (_pc : NonZero c) (_pe : NonZero e) :
    hsame (add (mul (mul c (add (mul (mul a x) b) d)) e) f)
      (add (mul (mul (mul c a) x) (mul b e)) (add (mul (mul c d) e) f)) := by
  -- BEDC touchpoint anchor: BHist hsame
  have expandedInner :
      hsame (mul c (add (mul (mul a x) b) d))
        (add (mul c (mul (mul a x) b)) (mul c d)) :=
    leftDistrib c (mul (mul a x) b) d
  have expandedWithE :
      hsame (mul (mul c (add (mul (mul a x) b) d)) e)
        (mul (add (mul c (mul (mul a x) b)) (mul c d)) e) :=
    mulCongr expandedInner (hsame_refl e)
  have distributedE :
      hsame (mul (add (mul c (mul (mul a x) b)) (mul c d)) e)
        (add (mul (mul c (mul (mul a x) b)) e) (mul (mul c d) e)) :=
    rightDistrib (mul c (mul (mul a x) b)) (mul c d) e
  have headExpanded :
      hsame (mul (mul c (add (mul (mul a x) b) d)) e)
        (add (mul (mul c (mul (mul a x) b)) e) (mul (mul c d) e)) :=
    hsame_trans expandedWithE distributedE
  have firstAssoc1 :
      hsame (mul c (mul (mul a x) b)) (mul (mul c (mul a x)) b) :=
    hsame_symm (assocC c (mul a x) b)
  have firstAssoc2 :
      hsame (mul c (mul a x)) (mul (mul c a) x) :=
    hsame_symm (assocC c a x)
  have firstAssoc3 :
      hsame (mul (mul c (mul a x)) b) (mul (mul (mul c a) x) b) :=
    mulCongr firstAssoc2 (hsame_refl b)
  have firstProductLeft :
      hsame (mul c (mul (mul a x) b)) (mul (mul (mul c a) x) b) :=
    hsame_trans firstAssoc1 firstAssoc3
  have firstProductWithE :
      hsame (mul (mul c (mul (mul a x) b)) e)
        (mul (mul (mul (mul c a) x) b) e) :=
    mulCongr firstProductLeft (hsame_refl e)
  have firstProductAssoc :
      hsame (mul (mul (mul (mul c a) x) b) e)
        (mul (mul (mul c a) x) (mul b e)) :=
    assocC (mul (mul c a) x) b e
  have firstProduct :
      hsame (mul (mul c (mul (mul a x) b)) e)
        (mul (mul (mul c a) x) (mul b e)) :=
    hsame_trans firstProductWithE firstProductAssoc
  have pairRewrite :
      hsame (add (mul (mul c (mul (mul a x) b)) e) (mul (mul c d) e))
        (add (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e)) :=
    addCongr firstProduct (hsame_refl (mul (mul c d) e))
  have beforeF :
      hsame (mul (mul c (add (mul (mul a x) b) d)) e)
        (add (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e)) :=
    hsame_trans headExpanded pairRewrite
  have addF :
      hsame (add (mul (mul c (add (mul (mul a x) b) d)) e) f)
        (add (add (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e)) f) :=
    addCongr beforeF (hsame_refl f)
  exact hsame_trans addF
    (addAssoc (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e) f)

end BEDC.Derived.FieldUp
