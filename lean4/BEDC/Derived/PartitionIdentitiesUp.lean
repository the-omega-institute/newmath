import BEDC.Derived.PartitionUp
import BEDC.Derived.PolygonalUp

namespace BEDC.Derived.PartitionIdentitiesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

private abbrev integerRing :
    BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

-- 有限 fuel 枚举非增分拆；fuel 只约束搜索树深度, 不伪装成无限完备性证明。
def partitionsFuel : Nat -> Nat -> Nat -> List (List Nat)
  | 0, _maxPart, _fuel => [[]]
  | Nat.succ _n, _maxPart, 0 => []
  | Nat.succ _n, 0, Nat.succ _fuel => []
  | Nat.succ n, Nat.succ maxPart, Nat.succ fuel =>
      let part := Nat.succ maxPart
      let withoutPart := partitionsFuel (Nat.succ n) maxPart fuel
      let withPart :=
        if part <= Nat.succ n then
          (partitionsFuel ((Nat.succ n) - part) part fuel).map
            (fun tail => part :: tail)
        else
          []
      withoutPart ++ withPart

def partitionFuelBudget (n : Nat) : Nat :=
  2 * n + 1

def partitionLists (n : Nat) : List (List Nat) :=
  partitionsFuel n n (partitionFuelBudget n)

def natEvenBool : Nat -> Bool
  | 0 => true
  | Nat.succ n => !natEvenBool n

def natOddBool (n : Nat) : Bool :=
  !natEvenBool n

def allOddParts : List Nat -> Bool
  | [] => true
  | part :: rest => natOddBool part && allOddParts rest

def containsNat (needle : Nat) : List Nat -> Bool
  | [] => false
  | part :: rest =>
      if part == needle then true else containsNat needle rest

def noRepeatedParts : List Nat -> Bool
  | [] => true
  | part :: rest => !containsNat part rest && noRepeatedParts rest

def countWhere {A : Type u} (p : A -> Bool) : List A -> Nat
  | [] => 0
  | x :: xs =>
      if p x then Nat.succ (countWhere p xs) else countWhere p xs

def oddPartPartitionCount (n : Nat) : Nat :=
  countWhere allOddParts (partitionLists n)

def distinctPartPartitionCount (n : Nat) : Nat :=
  countWhere noRepeatedParts (partitionLists n)

def positiveIntegerUpOfNat (n : Nat) : IntegerUp :=
  BEDC.Derived.RationalUp.intOfNat (natToUnary n) (natToUnary_unary n)

def signedIntegerUpOfNat (positive : Bool) (n : Nat) : IntegerUp :=
  if positive then
    positiveIntegerUpOfNat n
  else
    integerRing.neg (positiveIntegerUpOfNat n)

def generalizedPentagonalLower (k : Nat) : Nat :=
  BEDC.Derived.PolygonalUp.pentagonalNumber k

def generalizedPentagonalUpper (k : Nat) : Nat :=
  BEDC.Derived.PolygonalUp.pentagonalNumber k + k

def partitionNumberAtOffset (n g : Nat) : Nat :=
  if g <= n then
    BEDC.Derived.PartitionUp.partitionNumber (n - g)
  else
    0

def pentagonalPairContribution (n k : Nat) : Nat :=
  partitionNumberAtOffset n (generalizedPentagonalLower k) +
    partitionNumberAtOffset n (generalizedPentagonalUpper k)

def signedPentagonalPairContribution (n k : Nat) : IntegerUp :=
  signedIntegerUpOfNat (natOddBool k) (pentagonalPairContribution n k)

def pentagonalContributionListFrom :
    Nat -> Nat -> Nat -> List IntegerUp
  | _n, _next, 0 => []
  | n, next, Nat.succ fuel =>
      signedPentagonalPairContribution n next ::
        pentagonalContributionListFrom n (Nat.succ next) fuel

def pentagonalContributionList (n fuel : Nat) : List IntegerUp :=
  pentagonalContributionListFrom n 1 fuel

def pentagonalRecurrenceSum (n fuel : Nat) : IntegerUp :=
  BEDC.Algebra.FiniteFold.listSum integerRing
    (pentagonalContributionList n fuel)

theorem generalizedPentagonalLower_one :
    generalizedPentagonalLower 1 = 1 := by
  rfl

theorem generalizedPentagonalUpper_one :
    generalizedPentagonalUpper 1 = 2 := by
  rfl

theorem generalizedPentagonalLower_two :
    generalizedPentagonalLower 2 = 5 := by
  rfl

theorem generalizedPentagonalUpper_two :
    generalizedPentagonalUpper 2 = 7 := by
  rfl

theorem oddPartPartitionCount_zero :
    oddPartPartitionCount 0 = 1 := by
  rfl

theorem distinctPartPartitionCount_zero :
    distinctPartPartitionCount 0 = 1 := by
  rfl

theorem oddPartPartitionCount_five :
    oddPartPartitionCount 5 = 3 := by
  rfl

theorem distinctPartPartitionCount_five :
    distinctPartPartitionCount 5 = 3 := by
  rfl

theorem eulerOddDistinct_small_export :
    oddPartPartitionCount 0 = distinctPartPartitionCount 0 ∧
      oddPartPartitionCount 1 = distinctPartPartitionCount 1 ∧
      oddPartPartitionCount 2 = distinctPartPartitionCount 2 ∧
      oddPartPartitionCount 3 = distinctPartPartitionCount 3 ∧
      oddPartPartitionCount 4 = distinctPartPartitionCount 4 ∧
      oddPartPartitionCount 5 = distinctPartPartitionCount 5 ∧
      oddPartPartitionCount 6 = distinctPartPartitionCount 6 ∧
      oddPartPartitionCount 7 = distinctPartPartitionCount 7 ∧
      oddPartPartitionCount 8 = distinctPartPartitionCount 8 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · rfl

theorem eulerOddDistinct_small_values :
    oddPartPartitionCount 0 = 1 ∧
      oddPartPartitionCount 1 = 1 ∧
      oddPartPartitionCount 2 = 1 ∧
      oddPartPartitionCount 3 = 2 ∧
      oddPartPartitionCount 4 = 2 ∧
      oddPartPartitionCount 5 = 3 ∧
      oddPartPartitionCount 6 = 4 ∧
      oddPartPartitionCount 7 = 5 ∧
      oddPartPartitionCount 8 = 6 ∧
      distinctPartPartitionCount 8 = 6 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · constructor
                  · rfl
                  · rfl

theorem pentagonalRecurrence_one :
    IntEq (pentagonalRecurrenceSum 1 1)
      (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 1)) := by
  exact integerRing.refl _

theorem pentagonalRecurrence_two :
    IntEq (pentagonalRecurrenceSum 2 1)
      (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 2)) := by
  exact integerRing.refl _

theorem pentagonalRecurrence_three :
    IntEq (pentagonalRecurrenceSum 3 1)
      (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 3)) := by
  exact integerRing.refl _

theorem pentagonalRecurrence_four :
    IntEq (pentagonalRecurrenceSum 4 1)
      (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 4)) := by
  exact integerRing.refl _

theorem pentagonalRecurrence_five :
    IntEq (pentagonalRecurrenceSum 5 2)
      (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 5)) := by
  exact integerRing.refl _

theorem pentagonalRecurrence_six :
    IntEq (pentagonalRecurrenceSum 6 2)
      (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 6)) := by
  exact integerRing.refl _

theorem pentagonalRecurrence_small_export :
    IntEq (pentagonalRecurrenceSum 1 1)
        (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 1)) ∧
      IntEq (pentagonalRecurrenceSum 2 1)
        (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 2)) ∧
      IntEq (pentagonalRecurrenceSum 3 1)
        (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 3)) ∧
      IntEq (pentagonalRecurrenceSum 4 1)
        (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 4)) ∧
      IntEq (pentagonalRecurrenceSum 5 2)
        (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 5)) ∧
      IntEq (pentagonalRecurrenceSum 6 2)
        (positiveIntegerUpOfNat (BEDC.Derived.PartitionUp.partitionNumber 6)) := by
  constructor
  · exact pentagonalRecurrence_one
  · constructor
    · exact pentagonalRecurrence_two
    · constructor
      · exact pentagonalRecurrence_three
      · constructor
        · exact pentagonalRecurrence_four
        · constructor
          · exact pentagonalRecurrence_five
          · exact pentagonalRecurrence_six

end BEDC.Derived.PartitionIdentitiesUp
