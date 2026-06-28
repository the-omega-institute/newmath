import BEDC.Derived.PartitionIdentitiesUp
import BEDC.Derived.PolygonalNumberUp

namespace BEDC.Derived.PentagonalNumberTheoremUp

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

private abbrev integerRing :
    BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

abbrev positiveIntegerUpOfNat : Nat -> IntegerUp :=
  BEDC.Derived.PartitionIdentitiesUp.positiveIntegerUpOfNat

abbrev signedIntegerUpOfNat : Bool -> Nat -> IntegerUp :=
  BEDC.Derived.PartitionIdentitiesUp.signedIntegerUpOfNat

abbrev natEvenBool : Nat -> Bool :=
  BEDC.Derived.PartitionIdentitiesUp.natEvenBool

abbrev natOddBool : Nat -> Bool :=
  BEDC.Derived.PartitionIdentitiesUp.natOddBool

def intZero : IntegerUp :=
  BEDC.Algebra.Rel.intZero

def intOne : IntegerUp :=
  BEDC.Algebra.Rel.intOne

def intAdd (x y : IntegerUp) : IntegerUp :=
  integerRing.add x y

def intNeg (x : IntegerUp) : IntegerUp :=
  integerRing.neg x

def intSub (x y : IntegerUp) : IntegerUp :=
  intAdd x (intNeg y)

def natHalf : Nat -> Nat :=
  BEDC.Derived.PolygonalNumberUp.natHalf

-- 用项目内 `natHalf` 表示 $k(3k-1)/2$ 与 $k(3k+1)/2$。
def generalizedPentagonalNumber (k : Nat) : Nat :=
  natHalf (k * (3 * k - 1))

def generalizedPentagonalConjugateNumber (k : Nat) : Nat :=
  natHalf (k * (3 * k + 1))

def generalizedPentagonalPositive (k : Nat) : Nat :=
  BEDC.Derived.PartitionIdentitiesUp.generalizedPentagonalLower k

def generalizedPentagonalNegative (k : Nat) : Nat :=
  BEDC.Derived.PartitionIdentitiesUp.generalizedPentagonalUpper k

theorem generalizedPentagonalPositive_succ (k : Nat) :
    generalizedPentagonalPositive (Nat.succ k) =
      generalizedPentagonalPositive k + (3 * k + 1) := by
  rfl

theorem generalizedPentagonalNegative_def (k : Nat) :
    generalizedPentagonalNegative k = generalizedPentagonalPositive k + k := by
  rfl

structure GeneralizedPentagonalFormulaWindow : Prop where
  positive_one :
    generalizedPentagonalNumber 1 = generalizedPentagonalPositive 1
  negative_one :
    generalizedPentagonalConjugateNumber 1 = generalizedPentagonalNegative 1
  positive_two :
    generalizedPentagonalNumber 2 = generalizedPentagonalPositive 2
  negative_two :
    generalizedPentagonalConjugateNumber 2 = generalizedPentagonalNegative 2
  positive_three :
    generalizedPentagonalNumber 3 = generalizedPentagonalPositive 3
  negative_three :
    generalizedPentagonalConjugateNumber 3 = generalizedPentagonalNegative 3
  positive_four :
    generalizedPentagonalNumber 4 = generalizedPentagonalPositive 4
  negative_four :
    generalizedPentagonalConjugateNumber 4 = generalizedPentagonalNegative 4

theorem generalizedPentagonal_formula_window :
    GeneralizedPentagonalFormulaWindow := by
  exact {
    positive_one := rfl
    negative_one := rfl
    positive_two := rfl
    negative_two := rfl
    positive_three := rfl
    negative_three := rfl
    positive_four := rfl
    negative_four := rfl
  }

structure GeneralizedPentagonalSmallValues : Prop where
  positive_one : generalizedPentagonalPositive 1 = 1
  negative_one : generalizedPentagonalNegative 1 = 2
  positive_two : generalizedPentagonalPositive 2 = 5
  negative_two : generalizedPentagonalNegative 2 = 7
  positive_three : generalizedPentagonalPositive 3 = 12
  negative_three : generalizedPentagonalNegative 3 = 15
  positive_four : generalizedPentagonalPositive 4 = 22
  negative_four : generalizedPentagonalNegative 4 = 26

theorem generalizedPentagonal_small_values :
    GeneralizedPentagonalSmallValues := by
  exact {
    positive_one := rfl
    negative_one := rfl
    positive_two := rfl
    negative_two := rfl
    positive_three := rfl
    negative_three := rfl
    positive_four := rfl
    negative_four := rfl
  }

-- 系数递归忠实表示有限乘积 `∏_{i=1}^{factors} (1 - x^i)` 的第 `degree` 项。
def finiteEulerProductCoeff : Nat -> Nat -> IntegerUp
  | 0, 0 => intOne
  | 0, Nat.succ _degree => intZero
  | Nat.succ last, degree =>
      intSub (finiteEulerProductCoeff last degree)
        (if Nat.succ last <= degree then
          finiteEulerProductCoeff last (degree - Nat.succ last)
        else
          intZero)

theorem finiteEulerProductCoeff_zero_degree :
    finiteEulerProductCoeff 0 0 = intOne := by
  rfl

theorem finiteEulerProductCoeff_zero_positive_degree (degree : Nat) :
    finiteEulerProductCoeff 0 (Nat.succ degree) = intZero := by
  rfl

theorem finiteEulerProductCoeff_step (last degree : Nat) :
    finiteEulerProductCoeff (Nat.succ last) degree =
      intSub (finiteEulerProductCoeff last degree)
        (if Nat.succ last <= degree then
          finiteEulerProductCoeff last (degree - Nat.succ last)
        else
          intZero) := by
  rfl

def eulerPentagonalProductSign (k : Nat) : IntegerUp :=
  signedIntegerUpOfNat (natEvenBool k) 1

def eulerPentagonalSeriesHit (degree target k : Nat) : IntegerUp :=
  if degree == target then eulerPentagonalProductSign k else intZero

-- 有限搜索版右端: 常数项单独给出, 正负五边形数从 `1` 开始扫描。
def finiteEulerPentagonalSeriesCoeffFrom :
    Nat -> Nat -> Nat -> IntegerUp
  | _degree, _next, 0 => intZero
  | degree, next, Nat.succ fuel =>
      intAdd (eulerPentagonalSeriesHit degree (generalizedPentagonalPositive next) next)
        (intAdd (eulerPentagonalSeriesHit degree (generalizedPentagonalNegative next) next)
          (finiteEulerPentagonalSeriesCoeffFrom degree (Nat.succ next) fuel))

def finiteEulerPentagonalSeriesCoeff (degree fuel : Nat) : IntegerUp :=
  if degree == 0 then
    intOne
  else
    finiteEulerPentagonalSeriesCoeffFrom degree 1 fuel

def finiteEulerProductCoeffWindowFrom :
    Nat -> Nat -> Nat -> List IntegerUp
  | _factors, _start, 0 => []
  | factors, start, Nat.succ fuel =>
      finiteEulerProductCoeff factors start ::
        finiteEulerProductCoeffWindowFrom factors (Nat.succ start) fuel

def finiteEulerProductCoeffWindow (factors maxDegree : Nat) : List IntegerUp :=
  finiteEulerProductCoeffWindowFrom factors 0 (Nat.succ maxDegree)

def finiteEulerPentagonalSeriesCoeffWindowFrom :
    Nat -> Nat -> Nat -> List IntegerUp
  | _pentagonalFuel, _start, 0 => []
  | pentagonalFuel, start, Nat.succ fuel =>
      finiteEulerPentagonalSeriesCoeff start pentagonalFuel ::
        finiteEulerPentagonalSeriesCoeffWindowFrom pentagonalFuel (Nat.succ start) fuel

def finiteEulerPentagonalSeriesCoeffWindow
    (maxDegree pentagonalFuel : Nat) : List IntegerUp :=
  finiteEulerPentagonalSeriesCoeffWindowFrom pentagonalFuel 0 (Nat.succ maxDegree)

def coefficientProductFactorCount : Nat := 12

def coefficientWindowMaxDegree : Nat := 12

def coefficientPentagonalFuel : Nat := 4

private theorem listPairwiseRel_intRefl :
    (xs : List IntegerUp) -> BEDC.Algebra.FiniteFold.ListPairwiseRel IntEq xs xs
  | [] => BEDC.Algebra.FiniteFold.ListPairwiseRel.nil
  | x :: xs =>
      BEDC.Algebra.FiniteFold.ListPairwiseRel.cons
        (integerRing.refl x) (listPairwiseRel_intRefl xs)

theorem finiteEulerProduct_pentagonal_coefficients_window :
    BEDC.Algebra.FiniteFold.ListPairwiseRel IntEq
      (finiteEulerProductCoeffWindow coefficientProductFactorCount coefficientWindowMaxDegree)
      (finiteEulerPentagonalSeriesCoeffWindow coefficientWindowMaxDegree
        coefficientPentagonalFuel) := by
  unfold coefficientProductFactorCount coefficientWindowMaxDegree coefficientPentagonalFuel
  unfold finiteEulerProductCoeffWindow finiteEulerProductCoeffWindowFrom
  unfold finiteEulerPentagonalSeriesCoeffWindow finiteEulerPentagonalSeriesCoeffWindowFrom
  exact listPairwiseRel_intRefl _

def partitionPentagonalRecurrenceSum (n : Nat) : IntegerUp :=
  BEDC.Derived.PartitionIdentitiesUp.pentagonalRecurrenceSum n n

def partitionPentagonalRecurrenceClaim (n : Nat) : Prop :=
  IntEq (partitionPentagonalRecurrenceSum n)
    (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber n))

theorem pentagonalPartitionRecurrence_one :
    partitionPentagonalRecurrenceClaim 1 := by
  exact integerRing.refl _

theorem pentagonalPartitionRecurrence_two :
    partitionPentagonalRecurrenceClaim 2 := by
  exact integerRing.refl _

theorem pentagonalPartitionRecurrence_three :
    partitionPentagonalRecurrenceClaim 3 := by
  exact integerRing.refl _

theorem pentagonalPartitionRecurrence_four :
    partitionPentagonalRecurrenceClaim 4 := by
  exact integerRing.refl _

theorem pentagonalPartitionRecurrence_five :
    partitionPentagonalRecurrenceClaim 5 := by
  exact integerRing.refl _

theorem pentagonalPartitionRecurrence_six :
    partitionPentagonalRecurrenceClaim 6 := by
  exact integerRing.refl _

theorem pentagonalPartitionRecurrence_seven :
    partitionPentagonalRecurrenceClaim 7 := by
  exact integerRing.refl _

theorem pentagonalPartitionRecurrence_eight :
    partitionPentagonalRecurrenceClaim 8 := by
  exact integerRing.refl _

theorem pentagonalPartitionRecurrence_nine :
    partitionPentagonalRecurrenceClaim 9 := by
  exact integerRing.refl _

theorem pentagonalPartitionRecurrence_ten :
    partitionPentagonalRecurrenceClaim 10 := by
  exact integerRing.refl _

structure PartitionPentagonalRecurrenceSmallWindow : Prop where
  one : partitionPentagonalRecurrenceClaim 1
  two : partitionPentagonalRecurrenceClaim 2
  three : partitionPentagonalRecurrenceClaim 3
  four : partitionPentagonalRecurrenceClaim 4
  five : partitionPentagonalRecurrenceClaim 5
  six : partitionPentagonalRecurrenceClaim 6
  seven : partitionPentagonalRecurrenceClaim 7
  eight : partitionPentagonalRecurrenceClaim 8
  nine : partitionPentagonalRecurrenceClaim 9
  ten : partitionPentagonalRecurrenceClaim 10

theorem pentagonalPartitionRecurrence_small_window :
    PartitionPentagonalRecurrenceSmallWindow := by
  exact {
    one := pentagonalPartitionRecurrence_one
    two := pentagonalPartitionRecurrence_two
    three := pentagonalPartitionRecurrence_three
    four := pentagonalPartitionRecurrence_four
    five := pentagonalPartitionRecurrence_five
    six := pentagonalPartitionRecurrence_six
    seven := pentagonalPartitionRecurrence_seven
    eight := pentagonalPartitionRecurrence_eight
    nine := pentagonalPartitionRecurrence_nine
    ten := pentagonalPartitionRecurrence_ten
  }

structure PartitionNumberSmallValues : Prop where
  zero : BEDC.Derived.PartitionUp.partitionNumber 0 = 1
  one : BEDC.Derived.PartitionUp.partitionNumber 1 = 1
  two : BEDC.Derived.PartitionUp.partitionNumber 2 = 2
  three : BEDC.Derived.PartitionUp.partitionNumber 3 = 3
  four : BEDC.Derived.PartitionUp.partitionNumber 4 = 5
  five : BEDC.Derived.PartitionUp.partitionNumber 5 = 7
  six : BEDC.Derived.PartitionUp.partitionNumber 6 = 11
  seven : BEDC.Derived.PartitionUp.partitionNumber 7 = 15
  eight : BEDC.Derived.PartitionUp.partitionNumber 8 = 22
  nine : BEDC.Derived.PartitionUp.partitionNumber 9 = 30
  ten : BEDC.Derived.PartitionUp.partitionNumber 10 = 42

theorem partitionNumber_small_values :
    PartitionNumberSmallValues := by
  exact {
    zero := rfl
    one := rfl
    two := rfl
    three := rfl
    four := rfl
    five := rfl
    six := rfl
    seven := rfl
    eight := rfl
    nine := rfl
    ten := rfl
  }

structure PentagonalNumberTheoremUpFiniteExport : Prop where
  coefficient_window :
    BEDC.Algebra.FiniteFold.ListPairwiseRel IntEq
      (finiteEulerProductCoeffWindow coefficientProductFactorCount coefficientWindowMaxDegree)
      (finiteEulerPentagonalSeriesCoeffWindow coefficientWindowMaxDegree
        coefficientPentagonalFuel)
  recurrence_window : PartitionPentagonalRecurrenceSmallWindow

theorem PentagonalNumberTheoremUp_finite_export :
    PentagonalNumberTheoremUpFiniteExport := by
  exact {
    coefficient_window := finiteEulerProduct_pentagonal_coefficients_window
    recurrence_window := pentagonalPartitionRecurrence_small_window
  }

end BEDC.Derived.PentagonalNumberTheoremUp
