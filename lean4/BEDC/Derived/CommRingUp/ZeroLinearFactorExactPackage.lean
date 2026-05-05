import BEDC.Derived.CommRingUp.ZeroLinearFactor

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem commring_zero_linear_factor_exact_package {add mul : BHist -> BHist -> BHist}
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
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {a b : BHist} :
    (hsame (add a b) BHist.Empty ∨ hsame (add a (neg b)) BHist.Empty) ->
      hsame (mul (add a b) (add a (neg b))) BHist.Empty ∧
        hsame (mul a a) (mul b b) := by
  intro zeroFactor
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
  constructor
  · exact productZero
  · exact (commring_difference_of_squares_zero_exact addAssoc addComm zeroLeft negLeft
      addCongr mulCongr leftDistrib mulComm a b).mp productZero

protected theorem commring_zero_linear_factor_branch_exact_package_from_empty_unit
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
    (hsame (add a b) BHist.Empty ∨ hsame (add a (neg b)) BHist.Empty) ->
      (((hsame (add a b) BHist.Empty ∧ forall c : BHist,
          hsame (mul (add a b) c) BHist.Empty ∧
            hsame (mul c (add a b)) BHist.Empty) ∨
        (hsame (add a (neg b)) BHist.Empty ∧ forall c : BHist,
          hsame (mul (add a (neg b)) c) BHist.Empty ∧
            hsame (mul c (add a (neg b))) BHist.Empty)) ∧
        hsame (mul a a) (mul b b)) := by
  intro zeroFactor
  have branchPackage :
      ((hsame (add a b) BHist.Empty ∧ forall c : BHist,
          hsame (mul (add a b) c) BHist.Empty ∧
            hsame (mul c (add a b)) BHist.Empty) ∨
        (hsame (add a (neg b)) BHist.Empty ∧ forall c : BHist,
          hsame (mul (add a (neg b)) c) BHist.Empty ∧
            hsame (mul c (add a (neg b))) BHist.Empty)) :=
    commring_zero_linear_factor_annihilator_branch addAssoc zeroLeft negLeft addCongr
      mulComm mulCongr leftDistrib (a := a) (b := b) zeroFactor
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have exactPackage :
      hsame (mul (add a b) (add a (neg b))) BHist.Empty ∧
        hsame (mul a a) (mul b b) :=
    commring_zero_linear_factor_exact_package addAssoc addComm zeroLeft negLeft
      addCongr mulComm mulCongr leftDistrib rightDistrib (a := a) (b := b) zeroFactor
  constructor
  · exact branchPackage
  · exact exactPackage.right

end BEDC.Derived.CommRingUp
