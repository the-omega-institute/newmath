import BEDC.Derived.JacobiThetaFiniteUp
import BEDC.Derived.RationalUp

namespace BEDC.Derived.ThetaIdentitiesUp

open BEDC.Derived.RationalUp
open BEDC.Derived.JacobiThetaFiniteUp

abbrev Rat := RatNum

def ratSub (x y : Rat) : Rat :=
  ratAdd x (ratNeg y)

def natDouble (n : Nat) : Nat :=
  n + n

def natOddFromZero (n : Nat) : Nat :=
  Nat.succ (natDouble n)

def natEvenFromZero (n : Nat) : Nat :=
  Nat.succ (natOddFromZero n)

def zInvPow (z : Rat) (zNonzero : ratApart0 z) (n : Nat) : Rat :=
  ratPow (ratInvApart z zNonzero) n

def jacobiTripleProductFiniteFactor
    (q z : Rat) (zNonzero : ratApart0 z) (n : Nat) : Rat :=
  let odd := natOddFromZero n
  let even := natEvenFromZero n
  ratMul
    (ratSub ratOne (ratPow q even))
    (ratMul
      (ratAdd ratOne (ratMul (ratPow q odd) z))
      (ratAdd ratOne (ratMul (ratPow q odd) (ratInvApart z zNonzero))))

def jacobiTripleProductFiniteFrom
    (q z : Rat) (zNonzero : ratApart0 z) : Nat -> Nat -> Rat
  | _next, 0 => ratOne
  | next, Nat.succ fuel =>
      ratMul (jacobiTripleProductFiniteFactor q z zNonzero next)
        (jacobiTripleProductFiniteFrom q z zNonzero (Nat.succ next) fuel)

def jacobiTripleProductFinite
    (q z : Rat) (zNonzero : ratApart0 z) (fuel : Nat) : Rat :=
  jacobiTripleProductFiniteFrom q z zNonzero 0 fuel

def thetaLaurentPairTerm
    (q z : Rat) (zNonzero : ratApart0 z) (n : Nat) : Rat :=
  let exponent := n * n
  ratMul (ratPow q exponent)
    (ratAdd (ratPow z n) (zInvPow z zNonzero n))

def thetaLaurentSymmetricFiniteFrom
    (q z : Rat) (zNonzero : ratApart0 z) : Nat -> Nat -> Rat
  | _next, 0 => ratOne
  | next, Nat.succ fuel =>
      ratAdd (thetaLaurentPairTerm q z zNonzero next)
        (thetaLaurentSymmetricFiniteFrom q z zNonzero (Nat.succ next) fuel)

def thetaLaurentSymmetricFinite
    (q z : Rat) (zNonzero : ratApart0 z) (fuel : Nat) : Rat :=
  thetaLaurentSymmetricFiniteFrom q z zNonzero 1 fuel

def theta3FiniteFrom (q : Rat) : Nat -> Nat -> Rat
  | _next, 0 => ratOne
  | next, Nat.succ fuel =>
      ratAdd (ratMul ratTwo (ratPow q (next * next)))
        (theta3FiniteFrom q (Nat.succ next) fuel)

def theta3Finite (q : Rat) (fuel : Nat) : Rat :=
  theta3FiniteFrom q 1 fuel

def theta4FiniteFrom (q sign : Rat) : Nat -> Nat -> Rat
  | _next, 0 => ratOne
  | next, Nat.succ fuel =>
      ratAdd (ratMul ratTwo (ratMul sign (ratPow q (next * next))))
        (theta4FiniteFrom q (ratNeg sign) (Nat.succ next) fuel)

def theta4Finite (q : Rat) (fuel : Nat) : Rat :=
  theta4FiniteFrom q (ratNeg ratOne) 1 fuel

def theta2CoreFiniteFrom (q : Rat) : Nat -> Nat -> Rat
  | _next, 0 => ratZero
  | next, Nat.succ fuel =>
      ratAdd (ratPow q (next * Nat.succ next))
        (theta2CoreFiniteFrom q (Nat.succ next) fuel)

def theta2CoreFinite (q : Rat) (fuel : Nat) : Rat :=
  ratMul ratTwo (theta2CoreFiniteFrom q 0 fuel)

private theorem ratNum_zero_to_RatEq_zero {x : Rat} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

private theorem ratNeg_zero :
    RatEq (ratNeg ratZero) ratZero := by
  apply ratNum_zero_to_RatEq_zero
  unfold ratNeg ratZero intToRat
  change IntEq (IntNeg intZero) intZero
  exact IntEq_trans (IntEq_symm (IntAdd_zero (IntNeg intZero)))
    (IntAdd_neg_left intZero)

private theorem ratMul_zero_left (x : Rat) :
    RatEq (ratMul ratZero x) ratZero := by
  apply ratNum_zero_to_RatEq_zero
  unfold ratMul ratZero intToRat
  change IntEq (IntMul intZero x.num) intZero
  exact intMul_zero_left x.num

private theorem ratMul_zero_right (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  exact RatEq_trans (ratMul x ratZero) (ratMul ratZero x) ratZero
    (ratMul_comm x ratZero) (ratMul_zero_left x)

private theorem ratSub_zero_right (x : Rat) :
    RatEq (ratSub x ratZero) x := by
  unfold ratSub
  exact RatEq_trans (ratAdd x (ratNeg ratZero)) (ratAdd x ratZero) x
    (ratAdd_respects (RatEq_refl x) ratNeg_zero)
    (ratAdd_zero_right x)

private theorem ratPow_zero_one :
    RatEq (ratPow ratZero 1) ratZero :=
  ratPow_one ratZero

private theorem ratPow_zero_two :
    RatEq (ratPow ratZero 2) ratZero := by
  change RatEq (ratMul ratZero (ratPow ratZero 1)) ratZero
  exact ratMul_zero_left (ratPow ratZero 1)

private theorem jacobiTripleProductFiniteFactor_zero_window1
    (z : Rat) (zNonzero : ratApart0 z) :
    RatEq (jacobiTripleProductFiniteFactor ratZero z zNonzero 0) ratOne := by
  unfold jacobiTripleProductFiniteFactor natOddFromZero natEvenFromZero natDouble
  have minusPart : RatEq (ratSub ratOne (ratPow ratZero 2)) ratOne :=
    RatEq_trans (ratSub ratOne (ratPow ratZero 2)) (ratSub ratOne ratZero) ratOne
      (ratAdd_respects (RatEq_refl ratOne) (ratNeg_respects ratPow_zero_two))
      (ratSub_zero_right ratOne)
  have lowerPart :
      RatEq (ratAdd ratOne (ratMul (ratPow ratZero 1) z)) ratOne := by
    exact RatEq_trans
      (ratAdd ratOne (ratMul (ratPow ratZero 1) z))
      (ratAdd ratOne (ratMul ratZero z))
      ratOne
      (ratAdd_respects (RatEq_refl ratOne)
        (ratMul_respects ratPow_zero_one (RatEq_refl z)))
      (RatEq_trans
        (ratAdd ratOne (ratMul ratZero z))
        (ratAdd ratOne ratZero)
        ratOne
        (ratAdd_respects (RatEq_refl ratOne) (ratMul_zero_left z))
        (ratAdd_zero_right ratOne))
  have upperPart :
      RatEq
        (ratAdd ratOne (ratMul (ratPow ratZero 1) (ratInvApart z zNonzero)))
        ratOne := by
    exact RatEq_trans
      (ratAdd ratOne (ratMul (ratPow ratZero 1) (ratInvApart z zNonzero)))
      (ratAdd ratOne (ratMul ratZero (ratInvApart z zNonzero)))
      ratOne
      (ratAdd_respects (RatEq_refl ratOne)
        (ratMul_respects ratPow_zero_one
          (RatEq_refl (ratInvApart z zNonzero))))
      (RatEq_trans
        (ratAdd ratOne (ratMul ratZero (ratInvApart z zNonzero)))
        (ratAdd ratOne ratZero)
        ratOne
        (ratAdd_respects (RatEq_refl ratOne)
          (ratMul_zero_left (ratInvApart z zNonzero)))
        (ratAdd_zero_right ratOne))
  have plusProduct :
      RatEq
        (ratMul
          (ratAdd ratOne (ratMul (ratPow ratZero 1) z))
          (ratAdd ratOne (ratMul (ratPow ratZero 1) (ratInvApart z zNonzero))))
        ratOne := by
    exact RatEq_trans
      (ratMul
        (ratAdd ratOne (ratMul (ratPow ratZero 1) z))
        (ratAdd ratOne (ratMul (ratPow ratZero 1) (ratInvApart z zNonzero))))
      (ratMul ratOne ratOne)
      ratOne
      (ratMul_respects lowerPart upperPart)
      (ratOne_mul_left ratOne)
  exact RatEq_trans
    (ratMul
      (ratSub ratOne (ratPow ratZero 2))
      (ratMul
        (ratAdd ratOne (ratMul (ratPow ratZero 1) z))
        (ratAdd ratOne (ratMul (ratPow ratZero 1) (ratInvApart z zNonzero)))))
    (ratMul ratOne ratOne)
    ratOne
    (ratMul_respects minusPart plusProduct)
    (ratOne_mul_left ratOne)

private theorem thetaLaurentPairTerm_zero_window1
    (z : Rat) (zNonzero : ratApart0 z) :
    RatEq (thetaLaurentPairTerm ratZero z zNonzero 1) ratZero := by
  unfold thetaLaurentPairTerm
  exact RatEq_trans
    (ratMul (ratPow ratZero 1)
      (ratAdd (ratPow z 1) (zInvPow z zNonzero 1)))
    (ratMul ratZero
      (ratAdd (ratPow z 1) (zInvPow z zNonzero 1)))
    ratZero
    (ratMul_respects ratPow_zero_one
      (RatEq_refl (ratAdd (ratPow z 1) (zInvPow z zNonzero 1))))
    (ratMul_zero_left (ratAdd (ratPow z 1) (zInvPow z zNonzero 1)))

theorem jacobiTripleProductFinite_window0
    (q z : Rat) (zNonzero : ratApart0 z) :
    jacobiTripleProductFinite q z zNonzero 0 = ratOne := by
  rfl

theorem jacobiTripleProductFinite_one_factor
    (q z : Rat) (zNonzero : ratApart0 z) :
    RatEq (jacobiTripleProductFinite q z zNonzero 1)
      (jacobiTripleProductFiniteFactor q z zNonzero 0) := by
  unfold jacobiTripleProductFinite jacobiTripleProductFiniteFrom
  exact ratMul_one_right (jacobiTripleProductFiniteFactor q z zNonzero 0)

theorem thetaLaurentSymmetricFinite_window0
    (q z : Rat) (zNonzero : ratApart0 z) :
    thetaLaurentSymmetricFinite q z zNonzero 0 = ratOne := by
  rfl

theorem jacobiTripleProductFinite_matches_theta_window0
    (q z : Rat) (zNonzero : ratApart0 z) :
    RatEq (jacobiTripleProductFinite q z zNonzero 0)
      (thetaLaurentSymmetricFinite q z zNonzero 0) := by
  exact RatEq_refl ratOne

theorem jacobiTripleProductFinite_zeroBase_window1
    (z : Rat) (zNonzero : ratApart0 z) :
    RatEq (jacobiTripleProductFinite ratZero z zNonzero 1) ratOne := by
  exact RatEq_trans
    (jacobiTripleProductFinite ratZero z zNonzero 1)
    (jacobiTripleProductFiniteFactor ratZero z zNonzero 0)
    ratOne
    (jacobiTripleProductFinite_one_factor ratZero z zNonzero)
    (jacobiTripleProductFiniteFactor_zero_window1 z zNonzero)

theorem thetaLaurentSymmetricFinite_zeroBase_window1
    (z : Rat) (zNonzero : ratApart0 z) :
    RatEq (thetaLaurentSymmetricFinite ratZero z zNonzero 1) ratOne := by
  unfold thetaLaurentSymmetricFinite thetaLaurentSymmetricFiniteFrom
  exact RatEq_trans
    (ratAdd (thetaLaurentPairTerm ratZero z zNonzero 1) ratOne)
    (ratAdd ratZero ratOne)
    ratOne
    (ratAdd_respects (thetaLaurentPairTerm_zero_window1 z zNonzero)
      (RatEq_refl ratOne))
    (ratZero_add_left ratOne)

theorem jacobiTripleProductFinite_matches_theta_zeroBase_window1
    (z : Rat) (zNonzero : ratApart0 z) :
    RatEq (jacobiTripleProductFinite ratZero z zNonzero 1)
      (thetaLaurentSymmetricFinite ratZero z zNonzero 1) := by
  exact RatEq_trans
    (jacobiTripleProductFinite ratZero z zNonzero 1)
    ratOne
    (thetaLaurentSymmetricFinite ratZero z zNonzero 1)
    (jacobiTripleProductFinite_zeroBase_window1 z zNonzero)
    (RatEq_symm (thetaLaurentSymmetricFinite_zeroBase_window1 z zNonzero))

theorem theta3Finite_window0 (q : Rat) :
    theta3Finite q 0 = ratOne := by
  rfl

theorem theta4Finite_window0 (q : Rat) :
    theta4Finite q 0 = ratOne := by
  rfl

theorem theta2CoreFinite_window0 (q : Rat) :
    theta2CoreFiniteFrom q 0 0 = ratZero := by
  rfl

theorem theta3_theta4_window0 (q : Rat) :
    theta3Finite q 0 = theta4Finite q 0 := by
  rfl

theorem theta3Finite_one_unfold (q : Rat) :
    theta3Finite q 1 =
      ratAdd (ratMul ratTwo (ratPow q 1)) ratOne := by
  rfl

theorem theta4Finite_one_unfold (q : Rat) :
    theta4Finite q 1 =
      ratAdd (ratMul ratTwo (ratMul (ratNeg ratOne) (ratPow q 1))) ratOne := by
  rfl

theorem theta3Finite_zeroBase_window1 :
    RatEq (theta3Finite ratZero 1) ratOne := by
  unfold theta3Finite theta3FiniteFrom
  exact RatEq_trans
    (ratAdd (ratMul ratTwo (ratPow ratZero 1)) ratOne)
    (ratAdd ratZero ratOne)
    ratOne
    (ratAdd_respects
      (RatEq_trans
        (ratMul ratTwo (ratPow ratZero 1))
        (ratMul ratTwo ratZero)
        ratZero
        (ratMul_respects (RatEq_refl ratTwo) ratPow_zero_one)
        (ratMul_zero_right ratTwo))
      (RatEq_refl ratOne))
    (ratZero_add_left ratOne)

theorem theta4Finite_zeroBase_window1 :
    RatEq (theta4Finite ratZero 1) ratOne := by
  unfold theta4Finite theta4FiniteFrom
  exact RatEq_trans
    (ratAdd (ratMul ratTwo (ratMul (ratNeg ratOne) (ratPow ratZero 1)))
      ratOne)
    (ratAdd ratZero ratOne)
    ratOne
    (ratAdd_respects
      (RatEq_trans
        (ratMul ratTwo (ratMul (ratNeg ratOne) (ratPow ratZero 1)))
        (ratMul ratTwo ratZero)
        ratZero
        (ratMul_respects (RatEq_refl ratTwo)
          (RatEq_trans
            (ratMul (ratNeg ratOne) (ratPow ratZero 1))
            (ratMul (ratNeg ratOne) ratZero)
            ratZero
            (ratMul_respects (RatEq_refl (ratNeg ratOne)) ratPow_zero_one)
            (ratMul_zero_right (ratNeg ratOne))))
        (ratMul_zero_right ratTwo))
      (RatEq_refl ratOne))
    (ratZero_add_left ratOne)

theorem theta3_theta4_zeroBase_window1 :
    RatEq (theta3Finite ratZero 1) (theta4Finite ratZero 1) := by
  exact RatEq_trans
    (theta3Finite ratZero 1)
    ratOne
    (theta4Finite ratZero 1)
    theta3Finite_zeroBase_window1
    (RatEq_symm theta4Finite_zeroBase_window1)

theorem thetaIdentitiesFinite_export
    (q z : Rat) (zNonzero : ratApart0 z) :
    RatEq (jacobiTripleProductFinite q z zNonzero 0)
        (thetaLaurentSymmetricFinite q z zNonzero 0) ∧
      RatEq (jacobiTripleProductFinite ratZero z zNonzero 1)
        (thetaLaurentSymmetricFinite ratZero z zNonzero 1) ∧
      theta3Finite q 0 = theta4Finite q 0 ∧
      RatEq (theta3Finite ratZero 1) (theta4Finite ratZero 1) := by
  constructor
  · exact jacobiTripleProductFinite_matches_theta_window0 q z zNonzero
  · constructor
    · exact jacobiTripleProductFinite_matches_theta_zeroBase_window1 z zNonzero
    · constructor
      · exact theta3_theta4_window0 q
      · exact theta3_theta4_zeroBase_window1

end BEDC.Derived.ThetaIdentitiesUp
