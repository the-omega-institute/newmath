import BEDC.Derived.RingUp.Cancellation

namespace BEDC.Derived.RingUp
open BEDC.FKernel.Hist

theorem ring_zero_classifier_factor_absorption {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
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
    {x y : BHist} :
    hsame x BHist.Empty -> hsame (mul x y) BHist.Empty ∧
      hsame (mul y x) BHist.Empty := by
  intro xEmpty
  have zeroAbsorption :=
    ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  constructor
  · exact hsame_trans (mulCongr xEmpty (hsame_refl y)) (zeroAbsorption.right y)
  · exact hsame_trans (mulCongr (hsame_refl y) xEmpty) (zeroAbsorption.left y)

theorem ring_zero_classifier_signed_factor_absorption
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (negCongr : forall {a b : BHist}, hsame a b -> hsame (neg a) (neg b))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {x y : BHist} :
    hsame x BHist.Empty -> hsame (mul (neg x) y) BHist.Empty ∧
      hsame (mul y (neg x)) BHist.Empty ∧
      hsame (mul (neg x) (neg y)) BHist.Empty ∧
      hsame (mul (neg y) (neg x)) BHist.Empty := by
  intro xEmpty
  have negEmpty :
      hsame (neg x) BHist.Empty :=
    hsame_trans (negCongr xEmpty)
      (ring_neg_zero (add := add) (neg := neg) (zero := BHist.Empty) addComm zeroLeft negLeft)
  have plainAbsorption :=
    ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib (x := neg x) (y := y) negEmpty
  have signedAbsorption :=
    ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib (x := neg x) (y := neg y) negEmpty
  exact ⟨plainAbsorption.left, plainAbsorption.right,
    signedAbsorption.left, signedAbsorption.right⟩

theorem ring_zero_classifier_negated_product_annihilation
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (negCongr : forall {a b : BHist}, hsame a b -> hsame (neg a) (neg b))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {x y : BHist} :
    hsame x BHist.Empty ->
      hsame (neg (mul x y)) BHist.Empty ∧ hsame (neg (mul y x)) BHist.Empty := by
  intro xEmpty
  have signedAbsorption :=
    ring_zero_classifier_signed_factor_absorption addAssoc addComm zeroLeft negLeft addCongr
      mulCongr negCongr leftDistrib rightDistrib (x := x) (y := y) xEmpty
  have negLeftProduct :
      hsame (mul (neg x) y) (neg (mul x y)) :=
    ring_mul_neg_left_eq_neg_mul addAssoc addComm zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib x y
  have negRightProduct :
      hsame (mul y (neg x)) (neg (mul y x)) :=
    ring_mul_neg_right_eq_neg_mul addAssoc addComm zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib y x
  exact And.intro
    (hsame_trans (hsame_symm negLeftProduct) signedAbsorption.left)
    (hsame_trans (hsame_symm negRightProduct) signedAbsorption.right.left)

theorem ring_zero_classifier_two_sided_ideal_package {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (negCongr : forall {a b : BHist}, hsame a b -> hsame (neg a) (neg b))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) {x y z : BHist} :
    hsame x BHist.Empty -> hsame y BHist.Empty ->
      hsame (add x y) BHist.Empty ∧ hsame (neg x) BHist.Empty ∧
        hsame (mul x z) BHist.Empty ∧ hsame (mul z x) BHist.Empty ∧
          hsame (mul x y) BHist.Empty := by
  intro xEmpty yEmpty
  have addEmpty : hsame (add x y) BHist.Empty :=
    hsame_trans (addCongr xEmpty yEmpty) (zeroLeft BHist.Empty)
  have negEmpty : hsame (neg x) BHist.Empty :=
    hsame_trans (negCongr xEmpty)
      (ring_neg_zero (add := add) (neg := neg) (zero := BHist.Empty)
        addComm zeroLeft negLeft)
  have zAbsorption :=
    ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib (x := x) (y := z) xEmpty
  have yAbsorption :=
    ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib (x := x) (y := y) xEmpty
  exact And.intro addEmpty
    (And.intro negEmpty
      (And.intro zAbsorption.left (And.intro zAbsorption.right yAbsorption.left)))

theorem ring_signed_square_zero_ideal_package {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (negCongr : forall {a b : BHist}, hsame a b -> hsame (neg a) (neg b))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {x : BHist} :
    hsame x BHist.Empty -> hsame (mul (neg x) (neg x)) BHist.Empty ∧
      forall c : BHist, hsame (mul (mul (neg x) (neg x)) c) BHist.Empty ∧
        hsame (mul c (mul (neg x) (neg x))) BHist.Empty := by
  intro xEmpty
  have signedSquare :=
    ring_zero_classifier_signed_factor_absorption addAssoc addComm zeroLeft negLeft addCongr
      mulCongr negCongr leftDistrib rightDistrib (x := x) (y := x) xEmpty
  constructor
  · exact signedSquare.right.right.left
  · intro c
    exact
      ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
        leftDistrib rightDistrib (x := mul (neg x) (neg x)) (y := c)
        signedSquare.right.right.left

theorem ring_zero_classifier_square_annihilator_package {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
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
    {x : BHist} :
    hsame x BHist.Empty ->
      hsame (mul x x) BHist.Empty ∧
        forall c : BHist, hsame (mul (mul x x) c) BHist.Empty ∧
          hsame (mul c (mul x x)) BHist.Empty := by
  intro xEmpty
  have squareAbsorption :=
    ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib (x := x) (y := x) xEmpty
  constructor
  · exact squareAbsorption.left
  · intro c
    exact
      ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
        leftDistrib rightDistrib (x := mul x x) (y := c) squareAbsorption.left

theorem ring_equal_factor_difference_annihilation {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) {x y z : BHist} :
    hsame x y -> hsame (mul (add x (neg y)) z) BHist.Empty ∧
      hsame (mul z (add x (neg y))) BHist.Empty := by
  intro sameXY
  have differenceZero : hsame (add x (neg y)) BHist.Empty :=
    (ring_additive_difference_zero_exact addAssoc addComm zeroLeft negLeft addCongr).mpr sameXY
  exact ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
    leftDistrib rightDistrib (x := add x (neg y)) (y := z) differenceZero

theorem ring_equal_factor_signed_difference_annihilation {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (negCongr : forall {a b : BHist}, hsame a b -> hsame (neg a) (neg b))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {x y z : BHist} :
    hsame x y ->
      hsame (mul (add x (neg y)) z) BHist.Empty ∧
        hsame (mul z (add x (neg y))) BHist.Empty ∧
          hsame (mul (neg (add x (neg y))) z) BHist.Empty ∧
            hsame (mul z (neg (add x (neg y)))) BHist.Empty := by
  intro sameXY
  have differenceZero : hsame (add x (neg y)) BHist.Empty :=
    (ring_additive_difference_zero_exact addAssoc addComm zeroLeft negLeft addCongr).mpr
      sameXY
  have unsignedAbsorption :=
    ring_equal_factor_difference_annihilation addAssoc addComm zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib (x := x) (y := y) (z := z) sameXY
  have signedAbsorption :=
    ring_zero_classifier_signed_factor_absorption addAssoc addComm zeroLeft negLeft addCongr
      mulCongr negCongr leftDistrib rightDistrib (x := add x (neg y)) (y := z)
      differenceZero
  exact ⟨unsignedAbsorption.left, unsignedAbsorption.right, signedAbsorption.left,
    signedAbsorption.right.left⟩

end BEDC.Derived.RingUp
