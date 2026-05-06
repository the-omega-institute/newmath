import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem commring_zero_linear_factor_annihilator_branch {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    (hsame (add a b) BHist.Empty ∨ hsame (add a (neg b)) BHist.Empty) ->
      ((hsame (add a b) BHist.Empty ∧ forall c : BHist,
          hsame (mul (add a b) c) BHist.Empty ∧
            hsame (mul c (add a b)) BHist.Empty) ∨
        (hsame (add a (neg b)) BHist.Empty ∧ forall c : BHist,
          hsame (mul (add a (neg b)) c) BHist.Empty ∧
            hsame (mul c (add a (neg b))) BHist.Empty)) := by
  intro zeroFactor
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have zeroAbsorption :
      And (forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
        (forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty) :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  cases zeroFactor with
  | inl plusZero =>
      apply Or.inl
      constructor
      · exact plusZero
      · intro c
        constructor
        · exact hsame_trans
            (mulCongr plusZero (hsame_refl c))
            (zeroAbsorption.right c)
        · exact hsame_trans
            (mulCongr (hsame_refl c) plusZero)
            (zeroAbsorption.left c)
  | inr minusZero =>
      apply Or.inr
      constructor
      · exact minusZero
      · intro c
        constructor
        · exact hsame_trans
            (mulCongr minusZero (hsame_refl c))
            (zeroAbsorption.right c)
        · exact hsame_trans
            (mulCongr (hsame_refl c) minusZero)
            (zeroAbsorption.left c)

theorem commring_zero_linear_factor_commuted_signed_product_zero
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    (hsame (add a b) BHist.Empty ∨ hsame (add a (neg b)) BHist.Empty) ->
      hsame (mul (add a (neg b)) (add a b)) BHist.Empty := by
  intro zeroFactor
  have branches :=
    commring_zero_linear_factor_annihilator_branch addAssoc zeroLeft negLeft addCongr
      mulComm mulCongr leftDistrib (a := a) (b := b) zeroFactor
  cases branches with
  | inl plusBranch =>
      exact (plusBranch.right (add a (neg b))).right
  | inr minusBranch =>
      exact (minusBranch.right (add a b)).left

theorem commring_zero_linear_factor_signed_product_zero
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    (hsame (add a b) BHist.Empty ∨ hsame (add a (neg b)) BHist.Empty) ->
      hsame (mul (add a b) (add a (neg b))) BHist.Empty := by
  intro zeroFactor
  have branches :=
    commring_zero_linear_factor_annihilator_branch addAssoc zeroLeft negLeft addCongr
      mulComm mulCongr leftDistrib (a := a) (b := b) zeroFactor
  cases branches with
  | inl plusBranch =>
      exact (plusBranch.right (add a (neg b))).left
  | inr minusBranch =>
      exact (minusBranch.right (add a b)).right

theorem commring_equal_squares_commuted_signed_factor_zero
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    hsame (mul a a) (mul b b) ->
      hsame (mul (add a (neg b)) (add a b)) BHist.Empty := by
  intro sameSquares
  exact hsame_trans (mulComm (add a (neg b)) (add a b))
    (commring_equal_squares_signed_factor_zero addAssoc addComm zeroLeft negLeft
      addCongr mulComm mulCongr leftDistrib sameSquares)

theorem commring_zero_linear_factor_signed_product_annihilator_package
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    (hsame (add a b) BHist.Empty ∨ hsame (add a (neg b)) BHist.Empty) ->
      hsame (mul (add a b) (add a (neg b))) BHist.Empty ∧
        forall c : BHist,
          hsame (mul (mul (add a b) (add a (neg b))) c) BHist.Empty ∧
            hsame (mul c (mul (add a b) (add a (neg b)))) BHist.Empty := by
  intro zeroFactor
  have productZero : hsame (mul (add a b) (add a (neg b))) BHist.Empty :=
    commring_zero_linear_factor_signed_product_zero addAssoc zeroLeft negLeft addCongr
      mulComm mulCongr leftDistrib zeroFactor
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have zeroAbsorption :
      And (forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
        (forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty) :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  constructor
  · exact productZero
  · intro c
    constructor
    · exact hsame_trans
        (mulCongr productZero (hsame_refl c))
        (zeroAbsorption.right c)
    · exact hsame_trans
        (mulCongr (hsame_refl c) productZero)
        (zeroAbsorption.left c)

theorem commring_equal_squares_signed_product_annihilator
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    hsame (mul a a) (mul b b) ->
      hsame (mul (add a b) (add a (neg b))) BHist.Empty ∧
        forall c : BHist,
          hsame (mul (mul (add a b) (add a (neg b))) c) BHist.Empty ∧
            hsame (mul c (mul (add a b) (add a (neg b)))) BHist.Empty := by
  intro sameSquares
  have productZero : hsame (mul (add a b) (add a (neg b))) BHist.Empty :=
    commring_equal_squares_signed_factor_zero addAssoc addComm zeroLeft negLeft
      addCongr mulComm mulCongr leftDistrib sameSquares
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have zeroAbsorption :
      And (forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
        (forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty) :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  constructor
  · exact productZero
  · intro c
    constructor
    · exact hsame_trans
        (mulCongr productZero (hsame_refl c))
        (zeroAbsorption.right c)
    · exact hsame_trans
        (mulCongr (hsame_refl c) productZero)
        (zeroAbsorption.left c)

theorem commring_equal_squares_commuted_signed_product_annihilator
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    hsame (mul a a) (mul b b) ->
      hsame (mul (add a (neg b)) (add a b)) BHist.Empty ∧
        forall c : BHist,
          hsame (mul (mul (add a (neg b)) (add a b)) c) BHist.Empty ∧
            hsame (mul c (mul (add a (neg b)) (add a b))) BHist.Empty := by
  intro sameSquares
  have productZero : hsame (mul (add a (neg b)) (add a b)) BHist.Empty :=
    commring_equal_squares_commuted_signed_factor_zero addAssoc addComm zeroLeft negLeft
      addCongr mulComm mulCongr leftDistrib sameSquares
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have zeroAbsorption :
      And (forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
        (forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty) :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  constructor
  · exact productZero
  · intro c
    constructor
    · exact hsame_trans
        (mulCongr productZero (hsame_refl c))
        (zeroAbsorption.right c)
    · exact hsame_trans
        (mulCongr (hsame_refl c) productZero)
        (zeroAbsorption.left c)

theorem commring_equal_squares_bilateral_signed_product_context_annihilator
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    hsame (mul a a) (mul b b) -> forall c d : BHist,
      hsame (mul (mul c (mul (add a b) (add a (neg b)))) d) BHist.Empty ∧
        hsame (mul (mul c (mul (add a (neg b)) (add a b))) d) BHist.Empty := by
  intro sameSquares c d
  have forwardPackage :
      hsame (mul (add a b) (add a (neg b))) BHist.Empty ∧
        forall c : BHist,
          hsame (mul (mul (add a b) (add a (neg b))) c) BHist.Empty ∧
            hsame (mul c (mul (add a b) (add a (neg b)))) BHist.Empty :=
    commring_equal_squares_signed_product_annihilator addAssoc addComm zeroLeft
      negLeft addCongr mulComm mulCongr leftDistrib sameSquares
  have commutedPackage :
      hsame (mul (add a (neg b)) (add a b)) BHist.Empty ∧
        forall c : BHist,
          hsame (mul (mul (add a (neg b)) (add a b)) c) BHist.Empty ∧
            hsame (mul c (mul (add a (neg b)) (add a b))) BHist.Empty :=
    commring_equal_squares_commuted_signed_product_annihilator addAssoc addComm
      zeroLeft negLeft addCongr mulComm mulCongr leftDistrib sameSquares
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have zeroAbsorption :
      And (forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
        (forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty) :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  constructor
  · exact hsame_trans
      (mulCongr (forwardPackage.right c).right (hsame_refl d))
      (zeroAbsorption.right d)
  · exact hsame_trans
      (mulCongr (commutedPackage.right c).right (hsame_refl d))
      (zeroAbsorption.right d)

theorem commring_zero_linear_factor_equal_squares {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    (hsame (add a b) BHist.Empty ∨ hsame (add a (neg b)) BHist.Empty) ->
      hsame (mul a a) (mul b b) := by
  intro zeroFactor
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have zeroAbsorption :
      And (forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
        (forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty) :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  have productZero : hsame (mul (add a b) (add a (neg b))) BHist.Empty := by
    cases zeroFactor with
    | inl plusZero =>
        exact hsame_trans
          (mulCongr plusZero (hsame_refl (add a (neg b))))
          (zeroAbsorption.right (add a (neg b)))
    | inr minusZero =>
        exact hsame_trans
          (mulCongr (hsame_refl (add a b)) minusZero)
          (zeroAbsorption.left (add a b))
  exact (commring_difference_of_squares_zero_exact addAssoc addComm zeroLeft negLeft
    addCongr mulCongr leftDistrib mulComm a b).mp productZero

end BEDC.Derived.CommRingUp
