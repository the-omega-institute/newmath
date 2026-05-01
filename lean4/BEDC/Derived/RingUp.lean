import BEDC.FKernel.Hist
import BEDC.Derived.GroupUp
import BEDC.Derived.MonoidUp

namespace BEDC.Derived.RingUp

open BEDC.FKernel.Hist
open BEDC.Derived.MonoidUp

theorem ring_add_right_inverse {add : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {zero : BHist}
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero) :
    forall x : BHist, hsame (add x (neg x)) zero := by
  intro x
  exact hsame_trans (addComm x (neg x)) (negLeft x)

theorem ring_neg_zero {add : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {zero : BHist}
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero) :
    hsame (neg zero) zero := by
  exact hsame_trans (hsame_symm (zeroLeft (neg zero)))
    (hsame_trans (addComm zero (neg zero)) (negLeft zero))

theorem ring_add_duplicate_eq_zero {add : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b')) :
    forall a : BHist, hsame a (add a a) -> hsame a zero := by
  intro a duplicate
  have negStep : hsame (add (neg a) a) (add (neg a) (add a a)) := by
    exact addCongr (hsame_refl (neg a)) duplicate
  have assocBack : hsame (add (neg a) (add a a)) (add (add (neg a) a) a) := by
    exact hsame_symm (addAssoc (neg a) a a)
  have negToZeroAdd : hsame (add (add (neg a) a) a) (add zero a) := by
    exact addCongr (negLeft a) (hsame_refl a)
  have negToA : hsame (add (neg a) a) a := by
    exact hsame_trans negStep
      (hsame_trans assocBack (hsame_trans negToZeroAdd (zeroLeft a)))
  have zeroToA : hsame zero a := by
    exact hsame_trans (hsame_symm (negLeft a)) negToA
  exact hsame_symm zeroToA

theorem ring_add_right_zero {add : BHist -> BHist -> BHist} {zero : BHist}
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x) :
    forall x : BHist, hsame (add x zero) x := by
  intro x
  exact hsame_trans (addComm x zero) (zeroLeft x)

theorem ring_mul_zero_absorption {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    And (forall x : BHist, hsame (mul x zero) zero)
      (forall x : BHist, hsame (mul zero x) zero) := by
  constructor
  · intro x
    have zeroZero : hsame (add zero zero) zero := by
      exact zeroLeft zero
    have sameLeft : hsame (mul x (add zero zero)) (mul x zero) := by
      exact mulCongr (hsame_refl x) zeroZero
    have distrib : hsame (mul x (add zero zero)) (add (mul x zero) (mul x zero)) := by
      exact leftDistrib x zero zero
    have duplicate : hsame (mul x zero) (add (mul x zero) (mul x zero)) := by
      exact hsame_trans (hsame_symm sameLeft) distrib
    exact ring_add_duplicate_eq_zero addAssoc zeroLeft negLeft addCongr (mul x zero) duplicate
  · intro x
    have zeroZero : hsame (add zero zero) zero := by
      exact zeroLeft zero
    have sameLeft : hsame (mul (add zero zero) x) (mul zero x) := by
      exact mulCongr zeroZero (hsame_refl x)
    have distrib : hsame (mul (add zero zero) x) (add (mul zero x) (mul zero x)) := by
      exact rightDistrib zero zero x
    have duplicate : hsame (mul zero x) (add (mul zero x) (mul zero x)) := by
      exact hsame_trans (hsame_symm sameLeft) distrib
    exact ring_add_duplicate_eq_zero addAssoc zeroLeft negLeft addCongr (mul zero x) duplicate

theorem ring_mul_neg_left_inverse_sum_zero {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (add (mul (neg x) y) (mul x y)) zero := by
  have zeroAbsorption :=
    ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  intro x y
  have distrib :
      hsame (mul (add (neg x) x) y) (add (mul (neg x) y) (mul x y)) := by
    exact rightDistrib (neg x) x y
  have inverseProduct : hsame (mul (add (neg x) x) y) (mul zero y) := by
    exact mulCongr (negLeft x) (hsame_refl y)
  exact hsame_trans (hsame_symm distrib)
    (hsame_trans inverseProduct (zeroAbsorption.right y))

theorem ring_mul_neg_right_inverse_sum_zero {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (add (mul x (neg y)) (mul x y)) zero := by
  have zeroAbsorption :=
    ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  intro x y
  have distrib :
      hsame (mul x (add (neg y) y)) (add (mul x (neg y)) (mul x y)) := by
    exact leftDistrib x (neg y) y
  have inverseProduct : hsame (mul x (add (neg y) y)) (mul x zero) := by
    exact mulCongr (hsame_refl x) (negLeft y)
  exact hsame_trans (hsame_symm distrib)
    (hsame_trans inverseProduct (zeroAbsorption.left x))

theorem ring_mul_neg_left_right_same {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (mul (neg x) y) (mul x (neg y)) := by
  have addRightZero : forall x : BHist, hsame (add x zero) x := by
    exact ring_add_right_zero addComm zeroLeft
  have addRightInverse : forall x : BHist, hsame (add x (neg x)) zero := by
    exact ring_add_right_inverse addComm negLeft
  have leftNegative :
      forall x y : BHist, hsame (add (mul (neg x) y) (mul x y)) zero := by
    exact ring_mul_neg_left_inverse_sum_zero addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  have rightNegative :
      forall x y : BHist, hsame (add (mul x (neg y)) (mul x y)) zero := by
    exact ring_mul_neg_right_inverse_sum_zero addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  intro x y
  have sameProducts :
      hsame (add (mul (neg x) y) (mul x y)) (add (mul x (neg y)) (mul x y)) := by
    exact hsame_trans (leftNegative x y) (hsame_symm (rightNegative x y))
  exact BEDC.Derived.GroupUp.group_right_cancel addAssoc addRightZero addCongr addRightInverse
    sameProducts

theorem ring_mul_neg_left_eq_neg_mul {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (mul (neg x) y) (neg (mul x y)) := by
  intro x y
  have addRightZero : forall z : BHist, hsame (add z zero) z := by
    exact ring_add_right_zero addComm zeroLeft
  have leftSum :
      hsame (add (mul (neg x) y) (mul x y)) zero := by
    exact ring_mul_neg_left_inverse_sum_zero addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib x y
  have rightSum :
      hsame (add (mul x y) (neg (mul x y))) zero := by
    exact ring_add_right_inverse addComm negLeft (mul x y)
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    addAssoc
    zeroLeft
    addRightZero
    addCongr
    leftSum
    rightSum

theorem ring_mul_neg_right_eq_neg_mul {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (mul x (neg y)) (neg (mul x y)) := by
  intro x y
  have addRightZero : forall z : BHist, hsame (add z zero) z := by
    exact ring_add_right_zero addComm zeroLeft
  have zeroAbsorption :=
    ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  have leftSum :
      hsame (add (mul x (neg y)) (mul x y)) zero := by
    have distrib :
        hsame (mul x (add (neg y) y)) (add (mul x (neg y)) (mul x y)) := by
      exact leftDistrib x (neg y) y
    have inverseProduct : hsame (mul x (add (neg y) y)) (mul x zero) := by
      exact mulCongr (hsame_refl x) (negLeft y)
    exact hsame_trans (hsame_symm distrib)
      (hsame_trans inverseProduct (zeroAbsorption.left x))
  have rightSum :
      hsame (add (mul x y) (neg (mul x y))) zero := by
    exact ring_add_right_inverse addComm negLeft (mul x y)
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    addAssoc
    zeroLeft
    addRightZero
    addCongr
    leftSum
    rightSum

theorem ring_stability_certificate_fields {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero one : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (oneLeft : forall x : BHist, hsame (mul one x) x)
    (oneRight : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    ((forall x : BHist, MonoidClassifierSpec hsame x x) /\
      (forall {x y z : BHist}, MonoidClassifierSpec hsame x y ->
        MonoidClassifierSpec hsame y z ->
          MonoidClassifierSpec hsame x z) /\
      (forall x y z : BHist,
        MonoidClassifierSpec hsame (mul (mul x y) z) (mul x (mul y z))) /\
      (forall x : BHist, MonoidClassifierSpec hsame (mul one x) x) /\
      (forall x : BHist, MonoidClassifierSpec hsame (mul x one) x) /\
      (forall {a a' b b' : BHist}, MonoidClassifierSpec hsame a a' ->
        MonoidClassifierSpec hsame b b' ->
          MonoidClassifierSpec hsame (mul a b) (mul a' b'))) /\
      (forall x y z : BHist, hsame (add (add x y) z) (add x (add y z))) /\
      (forall x y : BHist, hsame (add x y) (add y x)) /\
      (forall x : BHist, hsame (add zero x) x) /\
      (forall x : BHist, hsame (add x zero) x) /\
      (forall x : BHist, hsame (add (neg x) x) zero) /\
      (forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
        hsame (add a b) (add a' b')) /\
      (forall x y z : BHist, hsame (mul x (add y z)) (add (mul x y) (mul x z))) /\
      (forall x y z : BHist, hsame (mul (add x y) z) (add (mul x z) (mul y z))) /\
      (forall x : BHist, hsame (mul x zero) zero) /\
      (forall x : BHist, hsame (mul zero x) zero) := by
  have addRightZero : forall x : BHist, hsame (add x zero) x := by
    intro x
    exact hsame_trans (addComm x zero) (zeroLeft x)
  have mulZeroRight : forall x : BHist, hsame (mul x zero) zero := by
    intro x
    have zeroZero : hsame (add zero zero) zero := by
      exact zeroLeft zero
    have sameLeft : hsame (mul x (add zero zero)) (mul x zero) := by
      exact mulCongr (hsame_refl x) zeroZero
    have distrib : hsame (mul x (add zero zero)) (add (mul x zero) (mul x zero)) := by
      exact leftDistrib x zero zero
    have duplicate : hsame (mul x zero) (add (mul x zero) (mul x zero)) := by
      exact hsame_trans (hsame_symm sameLeft) distrib
    exact ring_add_duplicate_eq_zero addAssoc zeroLeft negLeft addCongr (mul x zero) duplicate
  have mulZeroLeft : forall x : BHist, hsame (mul zero x) zero := by
    intro x
    have zeroZero : hsame (add zero zero) zero := by
      exact zeroLeft zero
    have sameLeft : hsame (mul (add zero zero) x) (mul zero x) := by
      exact mulCongr zeroZero (hsame_refl x)
    have distrib : hsame (mul (add zero zero) x) (add (mul zero x) (mul zero x)) := by
      exact rightDistrib zero zero x
    have duplicate : hsame (mul zero x) (add (mul zero x) (mul zero x)) := by
      exact hsame_trans (hsame_symm sameLeft) distrib
    exact ring_add_duplicate_eq_zero addAssoc zeroLeft negLeft addCongr (mul zero x) duplicate
  constructor
  · exact monoid_stability_certificate_fields
      hsame_refl
      hsame_trans
      mulAssoc
      oneLeft
      oneRight
      mulCongr
  · constructor
    · exact addAssoc
    · constructor
      · exact addComm
      · constructor
        · exact zeroLeft
        · constructor
          · exact addRightZero
          · constructor
            · exact negLeft
            · constructor
              · intro a a' b b' sameA sameB
                exact addCongr sameA sameB
              · constructor
                · exact leftDistrib
                · constructor
                  · exact rightDistrib
                  · constructor
                    · exact mulZeroRight
                    · exact mulZeroLeft

end BEDC.Derived.RingUp
