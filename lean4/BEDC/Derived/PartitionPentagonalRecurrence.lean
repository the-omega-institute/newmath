import BEDC.Derived.EulerPentagonalNumberTheorem

/-
Euler's pentagonal recurrence for the partition function p(n):

  p(n) = sum_{k >= 1} (-1)^(k-1)
    (p(n - k(3k-1)/2) + p(n - k(3k+1)/2))

with p(0)=1 and omitted negative-index terms.  This file records a finite
NameCert reconstruction of the classical Euler partition recurrence together
with the reciprocal relation

  (product (1 - q^n)) (sum p(n) q^n) = 1.

The polynomial side reuses the finite q-polynomial implementation from
EulerPentagonalNumberTheorem.  All certificates below are exact finite
kernel reductions, with no axiom introduced.
-/

namespace BEDC.Derived.PartitionPentagonalRecurrence

open BEDC.Derived.EulerPentagonalNumberTheorem

set_option maxRecDepth 6000

def recurrenceSign (k : Nat) : Int :=
  -signNat k

def partitionTerm (table : QPoly) (n g : Nat) : Int :=
  if g <= n then coeffAt table (n - g) else 0

def partitionPair (table : QPoly) (n k : Nat) : Int :=
  recurrenceSign k *
    (partitionTerm table n (pentagonalMinus k) +
      partitionTerm table n (pentagonalPlus k))

def partitionAccum (table : QPoly) (n : Nat) : Nat -> Nat -> Int
| 0, _ => 0
| fuel + 1, k =>
    if pentagonalMinus k <= n then
      partitionPair table n k + partitionAccum table n fuel (k + 1)
    else
      0

def partitionNext (table : QPoly) (n : Nat) : Int :=
  partitionAccum table n n 1

def partitionTable : Nat -> QPoly
| 0 => [1]
| n + 1 =>
    let table := partitionTable n
    table ++ [partitionNext table (n + 1)]

def partitionInt (n : Nat) : Int :=
  coeffAt (partitionTable n) n

def partition (n : Nat) : Nat :=
  Int.toNat (partitionInt n)

def partitionGF (N : Nat) : QPoly :=
  partitionTable N

def partitionValues20 : QPoly :=
  [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231,
    297, 385, 490, 627]

def reciprocalWindow21 : QPoly :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem partition_table_20 :
    partitionGF 20 = partitionValues20 := by
  rfl

theorem partition_0 : partition 0 = 1 := by
  rfl

theorem partition_1 : partition 1 = 1 := by
  rfl

theorem partition_2 : partition 2 = 2 := by
  rfl

theorem partition_3 : partition 3 = 3 := by
  rfl

theorem partition_4 : partition 4 = 5 := by
  rfl

theorem partition_5 : partition 5 = 7 := by
  rfl

theorem partition_6 : partition 6 = 11 := by
  rfl

theorem partition_7 : partition 7 = 15 := by
  rfl

theorem partition_8 : partition 8 = 22 := by
  rfl

theorem partition_9 : partition 9 = 30 := by
  rfl

theorem partition_10 : partition 10 = 42 := by
  rfl

theorem partition_11 : partition 11 = 56 := by
  rfl

theorem partition_12 : partition 12 = 77 := by
  rfl

theorem partition_13 : partition 13 = 101 := by
  rfl

theorem partition_14 : partition 14 = 135 := by
  rfl

theorem partition_15 : partition 15 = 176 := by
  rfl

theorem partition_16 : partition 16 = 231 := by
  rfl

theorem partition_17 : partition 17 = 297 := by
  rfl

theorem partition_18 : partition 18 = 385 := by
  rfl

theorem partition_19 : partition 19 = 490 := by
  rfl

theorem partition_20 : partition 20 = 627 := by
  rfl

theorem partition_pentagonal_recurrence_5 :
    (partition 5 : Int) =
      ((partition 4 : Int) + (partition 3 : Int)) -
        ((partition 0 : Int) + 0) := by
  rfl

theorem partition_pentagonal_recurrence_10 :
    (partition 10 : Int) =
      ((partition 9 : Int) + (partition 8 : Int)) -
        ((partition 5 : Int) + (partition 3 : Int)) := by
  rfl

theorem partition_pentagonal_recurrence_15 :
    (partition 15 : Int) =
      ((partition 14 : Int) + (partition 13 : Int)) -
        ((partition 10 : Int) + (partition 8 : Int)) +
          ((partition 3 : Int) + (partition 0 : Int)) := by
  rfl

theorem partition_pentagonal_recurrence_20 :
    (partition 20 : Int) =
      ((partition 19 : Int) + (partition 18 : Int)) -
        ((partition 15 : Int) + (partition 13 : Int)) +
          ((partition 8 : Int) + (partition 5 : Int)) := by
  rfl

theorem partition_reciprocal_window :
    ((qpmul (pentProd 20) (partitionGF 20)).take 21 == reciprocalWindow21) = true := by
  rfl

theorem partition_reciprocal_0 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 0 = 1 := by
  rfl

theorem partition_reciprocal_1 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 1 = 0 := by
  rfl

theorem partition_reciprocal_2 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 2 = 0 := by
  rfl

theorem partition_reciprocal_3 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 3 = 0 := by
  rfl

theorem partition_reciprocal_4 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 4 = 0 := by
  rfl

theorem partition_reciprocal_5 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 5 = 0 := by
  rfl

theorem partition_reciprocal_6 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 6 = 0 := by
  rfl

theorem partition_reciprocal_7 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 7 = 0 := by
  rfl

theorem partition_reciprocal_8 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 8 = 0 := by
  rfl

theorem partition_reciprocal_9 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 9 = 0 := by
  rfl

theorem partition_reciprocal_10 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 10 = 0 := by
  rfl

theorem partition_reciprocal_11 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 11 = 0 := by
  rfl

theorem partition_reciprocal_12 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 12 = 0 := by
  rfl

theorem partition_reciprocal_13 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 13 = 0 := by
  rfl

theorem partition_reciprocal_14 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 14 = 0 := by
  rfl

theorem partition_reciprocal_15 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 15 = 0 := by
  rfl

theorem partition_reciprocal_16 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 16 = 0 := by
  rfl

theorem partition_reciprocal_17 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 17 = 0 := by
  rfl

theorem partition_reciprocal_18 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 18 = 0 := by
  rfl

theorem partition_reciprocal_19 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 19 = 0 := by
  rfl

theorem partition_reciprocal_20 :
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 20 = 0 := by
  rfl

theorem partition_pentagonal_recurrence_certificate :
    partitionGF 20 = partitionValues20 ∧
    partition 6 = 11 ∧
    partition 10 = 42 ∧
    (partition 20 : Int) =
      ((partition 19 : Int) + (partition 18 : Int)) -
        ((partition 15 : Int) + (partition 13 : Int)) +
          ((partition 8 : Int) + (partition 5 : Int)) ∧
    ((qpmul (pentProd 20) (partitionGF 20)).take 21 == reciprocalWindow21) = true ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 0 = 1 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 1 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 2 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 3 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 4 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 5 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 6 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 7 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 8 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 9 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 10 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 11 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 12 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 13 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 14 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 15 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 16 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 17 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 18 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 19 = 0 ∧
    coeffAt (qpmul (pentProd 20) (partitionGF 20)) 20 = 0 := by
  constructor
  · exact partition_table_20
  constructor
  · exact partition_6
  constructor
  · exact partition_10
  constructor
  · exact partition_pentagonal_recurrence_20
  constructor
  · exact partition_reciprocal_window
  constructor
  · exact partition_reciprocal_0
  constructor
  · exact partition_reciprocal_1
  constructor
  · exact partition_reciprocal_2
  constructor
  · exact partition_reciprocal_3
  constructor
  · exact partition_reciprocal_4
  constructor
  · exact partition_reciprocal_5
  constructor
  · exact partition_reciprocal_6
  constructor
  · exact partition_reciprocal_7
  constructor
  · exact partition_reciprocal_8
  constructor
  · exact partition_reciprocal_9
  constructor
  · exact partition_reciprocal_10
  constructor
  · exact partition_reciprocal_11
  constructor
  · exact partition_reciprocal_12
  constructor
  · exact partition_reciprocal_13
  constructor
  · exact partition_reciprocal_14
  constructor
  · exact partition_reciprocal_15
  constructor
  · exact partition_reciprocal_16
  constructor
  · exact partition_reciprocal_17
  constructor
  · exact partition_reciprocal_18
  constructor
  · exact partition_reciprocal_19
  · exact partition_reciprocal_20

end BEDC.Derived.PartitionPentagonalRecurrence
