import BEDC.Algebra.FiniteFold
import BEDC.Derived.PartitionUp
import BEDC.Derived.RationalUp

namespace BEDC.Derived.JacobiThetaFiniteUp

open BEDC.Derived.RationalUp

abbrev Rat := RatNum

def ratTwo : Rat :=
  intToRat
    (intOfNat (BEDC.Derived.IntUp.natToUnary 2)
      (BEDC.Derived.IntUp.natToUnary_unary 2))

def ratPow (q : Rat) : Nat -> Rat
  | 0 => ratOne
  | Nat.succ n => ratMul q (ratPow q n)

def ratListSum : List Rat -> Rat
  | [] => ratZero
  | x :: xs => ratAdd x (ratListSum xs)

def ratListProd : List Rat -> Rat
  | [] => ratOne
  | x :: xs => ratMul x (ratListProd xs)

def thetaExponentSymmetric (n : Nat) : Nat :=
  n * n

def theta3FiniteTerm (q : Rat) (n : Nat) : Rat :=
  ratPow q (thetaExponentSymmetric n)

def theta3FiniteTailTermsFrom (q : Rat) : Nat -> Nat -> List Rat
  | _next, 0 => []
  | next, Nat.succ fuel =>
      theta3FiniteTerm q next ::
        theta3FiniteTailTermsFrom q (Nat.succ next) fuel

def theta3FiniteTailTerms (q : Rat) (fuel : Nat) : List Rat :=
  theta3FiniteTailTermsFrom q 1 fuel

-- 有限截断只记录 `1 + 2 * (q^1 + q^4 + ... + q^{N^2})`。
def theta3Finite (q : Rat) (fuel : Nat) : Rat :=
  ratAdd ratOne
    (ratMul ratTwo (ratListSum (theta3FiniteTailTerms q fuel)))

def jacobiFactorMinus (q : Rat) (n : Nat) : Rat :=
  ratAdd ratOne (ratNeg (ratPow q n))

def jacobiFactorPlusLower (q z : Rat) (n : Nat) : Rat :=
  ratAdd ratOne (ratMul z (ratPow q n))

def jacobiFactorPlusUpper (q z : Rat) (z_nonzero : ratApart0 z) (n : Nat) : Rat :=
  ratAdd ratOne (ratMul (ratInvApart z z_nonzero) (ratPow q (Nat.succ n)))

def jacobiTripleProductFactor (q z : Rat) (z_nonzero : ratApart0 z) (n : Nat) : Rat :=
  ratMul (jacobiFactorMinus q (Nat.succ n))
    (ratMul (jacobiFactorPlusLower q z n)
      (jacobiFactorPlusUpper q z z_nonzero n))

def jacobiTripleProductFiniteFrom
    (q z : Rat) (z_nonzero : ratApart0 z) : Nat -> Nat -> Rat
  | _next, 0 => ratOne
  | next, Nat.succ fuel =>
      ratMul (jacobiTripleProductFactor q z z_nonzero next)
        (jacobiTripleProductFiniteFrom q z z_nonzero (Nat.succ next) fuel)

def jacobiTripleProductFinite
    (q z : Rat) (z_nonzero : ratApart0 z) (fuel : Nat) : Rat :=
  jacobiTripleProductFiniteFrom q z z_nonzero 0 fuel

def integerSquare (n : Nat) : Nat :=
  n * n

def squareRepresentationCount (m fuel : Nat) : Nat :=
  List.count m ((List.range (fuel + 1)).map integerSquare)

def thetaSquareCoefficient (m fuel : Nat) : Nat :=
  if m == 0 then
    1
  else
    2 * squareRepresentationCount m fuel

def partitionThetaSquareLink (m fuel : Nat) : Nat :=
  thetaSquareCoefficient m fuel *
    BEDC.Derived.PartitionUp.partitionNumber m

def partitionThetaCoefficientFrom (m fuel : Nat) : Nat -> Nat -> Nat
  | _k, 0 => 0
  | k, Nat.succ remaining =>
      thetaSquareCoefficient k fuel *
          BEDC.Derived.PartitionUp.partitionNumber (m - k) +
        partitionThetaCoefficientFrom m fuel (Nat.succ k) remaining

def partitionThetaCoefficient (m fuel : Nat) : Nat :=
  partitionThetaCoefficientFrom m fuel 0 (Nat.succ m)

theorem ratPow_zero (q : Rat) :
    ratPow q 0 = ratOne := by
  rfl

theorem ratPow_one (q : Rat) :
    RatEq (ratPow q 1) q := by
  exact ratMul_one_right q

theorem ratListSum_nil :
    ratListSum [] = ratZero := by
  rfl

theorem ratListProd_nil :
    ratListProd [] = ratOne := by
  rfl

theorem theta3Finite_zero :
    theta3Finite ratZero 0 = ratOne := by
  rfl

theorem theta3Finite_tail_terms_one (q : Rat) :
    theta3FiniteTailTerms q 1 = [ratPow q 1] := by
  rfl

theorem theta3Finite_one_unfold (q : Rat) :
    theta3Finite q 1 =
      ratAdd ratOne (ratMul ratTwo (ratAdd (ratPow q 1) ratZero)) := by
  rfl

theorem theta3Finite_one_term (q : Rat) :
    RatEq (theta3Finite q 1)
      (ratAdd ratOne (ratMul ratTwo q)) := by
  unfold theta3Finite theta3FiniteTailTerms theta3FiniteTailTermsFrom
  exact ratAdd_respects (RatEq_refl ratOne)
    (ratMul_respects (RatEq_refl ratTwo)
      (RatEq_trans (ratListSum [ratPow q 1]) (ratPow q 1) q
        (ratAdd_zero_right (ratPow q 1)) (ratPow_one q)))

theorem jacobiTripleProductFinite_zero
    (q z : Rat) (z_nonzero : ratApart0 z) :
    jacobiTripleProductFinite q z z_nonzero 0 = ratOne := by
  rfl

theorem jacobiTripleProductFinite_one
    (q z : Rat) (z_nonzero : ratApart0 z) :
    RatEq (jacobiTripleProductFinite q z z_nonzero 1)
      (jacobiTripleProductFactor q z z_nonzero 0) := by
  unfold jacobiTripleProductFinite jacobiTripleProductFiniteFrom
  exact ratMul_one_right (jacobiTripleProductFactor q z z_nonzero 0)

theorem theta3Finite_one_symmetric_term (q : Rat) :
    RatEq (theta3Finite q 1)
      (ratAdd ratOne (ratMul ratTwo (ratPow q 1))) := by
  exact RatEq_trans (theta3Finite q 1)
    (ratAdd ratOne (ratMul ratTwo q))
    (ratAdd ratOne (ratMul ratTwo (ratPow q 1)))
    (theta3Finite_one_term q)
    (ratAdd_respects (RatEq_refl ratOne)
      (ratMul_respects (RatEq_refl ratTwo) (RatEq_symm (ratPow_one q))))

theorem squareRepresentationCount_zero_zero :
    squareRepresentationCount 0 0 = 1 := by
  rfl

theorem squareRepresentationCount_one_one :
    squareRepresentationCount 1 1 = 1 := by
  rfl

theorem thetaSquareCoefficient_zero (fuel : Nat) :
    thetaSquareCoefficient 0 fuel = 1 := by
  rfl

theorem thetaSquareCoefficient_one_one :
    thetaSquareCoefficient 1 1 = 2 := by
  rfl

theorem partitionThetaSquareLink_zero :
    partitionThetaSquareLink 0 0 = 1 := by
  rfl

theorem partitionThetaSquareLink_one :
    partitionThetaSquareLink 1 1 = 2 := by
  rfl

theorem partitionThetaCoefficient_zero :
    partitionThetaCoefficient 0 0 = 1 := by
  rfl

theorem partitionThetaCoefficient_one :
    partitionThetaCoefficient 1 1 = 3 := by
  rfl

theorem jacobiThetaFinite_export :
    theta3Finite ratZero 0 = ratOne ∧
      squareRepresentationCount 0 0 = 1 ∧
      thetaSquareCoefficient 1 1 = 2 ∧
      partitionThetaSquareLink 1 1 = 2 ∧
      partitionThetaCoefficient 1 1 = 3 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl

end BEDC.Derived.JacobiThetaFiniteUp
