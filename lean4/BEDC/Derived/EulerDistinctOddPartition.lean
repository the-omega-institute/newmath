/-
Euler's distinct-equals-odd partition identity

  #{partitions of n into distinct parts}
    = #{partitions of n into odd parts}

has generating-function form

  product_{n >= 1} (1 + q^n) = product_{n >= 1} 1 / (1 - q^(2*n - 1)).

This file records an exact finite NameCert reconstruction of the
Euler--Glaisher theorem.  The partition enumerators are finite list programs,
the product side uses the q-polynomial operations from the Euler pentagonal
certificate, and the checked window is n <= 12.  Glaisher's bijection is
encoded as the binary carry map from odd parts to distinct parts and the
reverse odd-kernel expansion.  No axiom is introduced; all displayed checks
are kernel reduction over finite data.
-/

import BEDC.Derived.EulerPentagonalNumberTheorem

namespace BEDC.Derived.EulerDistinctOddPartition

set_option maxRecDepth 3000

abbrev QPoly := BEDC.Derived.EulerPentagonalNumberTheorem.QPoly

def qpmul : QPoly -> QPoly -> QPoly :=
  BEDC.Derived.EulerPentagonalNumberTheorem.qpmul

def zeroes : Nat -> QPoly :=
  BEDC.Derived.EulerPentagonalNumberTheorem.zeroes

def coeffAt : QPoly -> Nat -> Int :=
  BEDC.Derived.EulerPentagonalNumberTheorem.coeffAt

def distinctPartitionsAtMost : Nat -> Nat -> List (List Nat)
| n, 0 =>
    if n == 0 then
      [[]]
    else
      []
| n, m + 1 =>
    let withoutHead := distinctPartitionsAtMost n m
    let withHead :=
      if m + 1 <= n then
        (distinctPartitionsAtMost (n - (m + 1)) m).map (fun p => (m + 1) :: p)
      else
        []
    withHead ++ withoutHead

def distinctPartitions (n : Nat) : List (List Nat) :=
  distinctPartitionsAtMost n n

def distinctCount (n : Nat) : Nat :=
  (distinctPartitions n).length

def oddPartitionsFuel : Nat -> Nat -> Nat -> List (List Nat)
| n, _, 0 =>
    if n == 0 then
      [[]]
    else
      []
| n, 0, _ + 1 =>
    if n == 0 then
      [[]]
    else
      []
| n, m + 1, fuel + 1 =>
    let withoutHead := oddPartitionsFuel n m fuel
    let withHead :=
      if m + 1 <= n then
        if (m + 1) % 2 == 1 then
          (oddPartitionsFuel (n - (m + 1)) (m + 1) fuel).map
            (fun p => (m + 1) :: p)
        else
          []
      else
        []
    withHead ++ withoutHead

def oddPartitions (n : Nat) : List (List Nat) :=
  oddPartitionsFuel n n (2 * n + 1)

def oddCount (n : Nat) : Nat :=
  (oddPartitions n).length

theorem distinctPartitions_6_concrete :
    distinctPartitions 6 = [[6], [5, 1], [4, 2], [3, 2, 1]] := by
  rfl

theorem oddPartitions_6_concrete :
    oddPartitions 6 = [[5, 1], [3, 3], [3, 1, 1, 1], [1, 1, 1, 1, 1, 1]] := by
  rfl

theorem distinctCount_6_concrete : distinctCount 6 = 4 := by
  rfl

theorem oddCount_6_concrete : oddCount 6 = 4 := by
  rfl

theorem distinct_eq_odd_1 : distinctCount 1 = oddCount 1 := by
  rfl

theorem distinct_eq_odd_2 : distinctCount 2 = oddCount 2 := by
  rfl

theorem distinct_eq_odd_3 : distinctCount 3 = oddCount 3 := by
  rfl

theorem distinct_eq_odd_4 : distinctCount 4 = oddCount 4 := by
  rfl

theorem distinct_eq_odd_5 : distinctCount 5 = oddCount 5 := by
  rfl

theorem distinct_eq_odd_6 : distinctCount 6 = oddCount 6 := by
  rfl

theorem distinct_eq_odd_7 : distinctCount 7 = oddCount 7 := by
  rfl

theorem distinct_eq_odd_8 : distinctCount 8 = oddCount 8 := by
  rfl

theorem distinct_eq_odd_9 : distinctCount 9 = oddCount 9 := by
  rfl

theorem distinct_eq_odd_10 : distinctCount 10 = oddCount 10 := by
  rfl

theorem distinct_eq_odd_11 : distinctCount 11 = oddCount 11 := by
  rfl

theorem distinct_eq_odd_12 : distinctCount 12 = oddCount 12 := by
  rfl

def onePlusQFactor (n : Nat) : QPoly :=
  1 :: zeroes (n - 1) ++ [1]

def distinctGF : Nat -> QPoly
| 0 => [1]
| n + 1 => qpmul (distinctGF n) (onePlusQFactor (n + 1))

def distinctGF12CoeffTable : List Int :=
  [1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15]

theorem distinctGF12_coeff_table :
    ((distinctGF 12).take 13 == distinctGF12CoeffTable) = true := by
  rfl

theorem distinctGF12_coeff_0 : coeffAt (distinctGF 12) 0 = distinctCount 0 := by
  rfl

theorem distinctGF12_coeff_1 : coeffAt (distinctGF 12) 1 = distinctCount 1 := by
  rfl

theorem distinctGF12_coeff_2 : coeffAt (distinctGF 12) 2 = distinctCount 2 := by
  rfl

theorem distinctGF12_coeff_3 : coeffAt (distinctGF 12) 3 = distinctCount 3 := by
  rfl

theorem distinctGF12_coeff_4 : coeffAt (distinctGF 12) 4 = distinctCount 4 := by
  rfl

theorem distinctGF12_coeff_5 : coeffAt (distinctGF 12) 5 = distinctCount 5 := by
  rfl

theorem distinctGF12_coeff_6 : coeffAt (distinctGF 12) 6 = distinctCount 6 := by
  rfl

theorem distinctGF12_coeff_7 : coeffAt (distinctGF 12) 7 = distinctCount 7 := by
  rfl

theorem distinctGF12_coeff_8 : coeffAt (distinctGF 12) 8 = distinctCount 8 := by
  rfl

theorem distinctGF12_coeff_9 : coeffAt (distinctGF 12) 9 = distinctCount 9 := by
  rfl

theorem distinctGF12_coeff_10 : coeffAt (distinctGF 12) 10 = distinctCount 10 := by
  rfl

theorem distinctGF12_coeff_11 : coeffAt (distinctGF 12) 11 = distinctCount 11 := by
  rfl

theorem distinctGF12_coeff_12 : coeffAt (distinctGF 12) 12 = distinctCount 12 := by
  rfl

def addDistinctPartAscending (a : Nat) : List Nat -> List Nat
| [] => [a]
| b :: bs =>
    if a == b then
      addDistinctPartAscending (2 * a) bs
    else if a <= b then
      a :: b :: bs
    else
      b :: addDistinctPartAscending a bs

def glaisherOddToDistinctAscending : List Nat -> List Nat
| [] => []
| a :: as => addDistinctPartAscending a (glaisherOddToDistinctAscending as)

def reverseNat : List Nat -> List Nat
| [] => []
| a :: as => reverseNat as ++ [a]

def glaisherOddToDistinct (p : List Nat) : List Nat :=
  reverseNat (glaisherOddToDistinctAscending p)

def repeatNat (a : Nat) : Nat -> List Nat
| 0 => []
| n + 1 => a :: repeatNat a n

def oddKernelCopiesFuel : Nat -> Nat -> Nat -> List Nat
| 0, _, _ => []
| fuel + 1, part, copies =>
    if part == 0 then
      []
    else if part % 2 == 0 then
      oddKernelCopiesFuel fuel (part / 2) (2 * copies)
    else
      repeatNat part copies

def splitPartToOdd (part : Nat) : List Nat :=
  oddKernelCopiesFuel part part 1

def glaisherDistinctToOdd : List Nat -> List Nat
| [] => []
| a :: as => splitPartToOdd a ++ glaisherDistinctToOdd as

def sumList : List Nat -> Nat
| [] => 0
| a :: as => a + sumList as

theorem glaisher_odd_to_distinct_6_concrete :
    glaisherOddToDistinct [5, 1] = [5, 1] := by
  rfl

theorem glaisher_odd_to_distinct_six_ones_concrete :
    glaisherOddToDistinct [1, 1, 1, 1, 1, 1] = [4, 2] := by
  rfl

theorem glaisher_distinct_to_odd_6_concrete :
    glaisherDistinctToOdd [6] = [3, 3] := by
  rfl

theorem glaisher_distinct_to_odd_4_2_concrete :
    glaisherDistinctToOdd [4, 2] = [1, 1, 1, 1, 1, 1] := by
  rfl

theorem glaisher_roundtrip_odd_5_1 :
    glaisherDistinctToOdd (glaisherOddToDistinct [5, 1]) = [5, 1] := by
  rfl

theorem glaisher_roundtrip_odd_3_3 :
    glaisherDistinctToOdd (glaisherOddToDistinct [3, 3]) = [3, 3] := by
  rfl

theorem glaisher_roundtrip_odd_3_1_1_1 :
    glaisherDistinctToOdd (glaisherOddToDistinct [3, 1, 1, 1]) =
      [3, 1, 1, 1] := by
  rfl

theorem glaisher_roundtrip_odd_six_ones :
    glaisherDistinctToOdd (glaisherOddToDistinct [1, 1, 1, 1, 1, 1]) =
      [1, 1, 1, 1, 1, 1] := by
  rfl

theorem glaisher_sum_odd_3_1_1_1 :
    sumList (glaisherOddToDistinct [3, 1, 1, 1]) = sumList [3, 1, 1, 1] := by
  rfl

theorem glaisher_sum_distinct_4_2 :
    sumList (glaisherDistinctToOdd [4, 2]) = sumList [4, 2] := by
  rfl

theorem euler_distinct_odd_partition_certificate :
    distinctCount 1 = oddCount 1 ∧
    distinctCount 2 = oddCount 2 ∧
    distinctCount 3 = oddCount 3 ∧
    distinctCount 4 = oddCount 4 ∧
    distinctCount 5 = oddCount 5 ∧
    distinctCount 6 = oddCount 6 ∧
    distinctCount 7 = oddCount 7 ∧
    distinctCount 8 = oddCount 8 ∧
    distinctCount 9 = oddCount 9 ∧
    distinctCount 10 = oddCount 10 ∧
    distinctCount 11 = oddCount 11 ∧
    distinctCount 12 = oddCount 12 ∧
    ((distinctGF 12).take 13 == distinctGF12CoeffTable) = true ∧
    coeffAt (distinctGF 12) 0 = distinctCount 0 ∧
    coeffAt (distinctGF 12) 6 = distinctCount 6 ∧
    coeffAt (distinctGF 12) 12 = distinctCount 12 ∧
    glaisherDistinctToOdd (glaisherOddToDistinct [5, 1]) = [5, 1] ∧
    glaisherDistinctToOdd (glaisherOddToDistinct [3, 3]) = [3, 3] ∧
    glaisherDistinctToOdd (glaisherOddToDistinct [3, 1, 1, 1]) =
      [3, 1, 1, 1] ∧
    glaisherDistinctToOdd (glaisherOddToDistinct [1, 1, 1, 1, 1, 1]) =
      [1, 1, 1, 1, 1, 1] ∧
    sumList (glaisherOddToDistinct [3, 1, 1, 1]) = sumList [3, 1, 1, 1] ∧
    sumList (glaisherDistinctToOdd [4, 2]) = sumList [4, 2] := by
  constructor
  · exact distinct_eq_odd_1
  constructor
  · exact distinct_eq_odd_2
  constructor
  · exact distinct_eq_odd_3
  constructor
  · exact distinct_eq_odd_4
  constructor
  · exact distinct_eq_odd_5
  constructor
  · exact distinct_eq_odd_6
  constructor
  · exact distinct_eq_odd_7
  constructor
  · exact distinct_eq_odd_8
  constructor
  · exact distinct_eq_odd_9
  constructor
  · exact distinct_eq_odd_10
  constructor
  · exact distinct_eq_odd_11
  constructor
  · exact distinct_eq_odd_12
  constructor
  · exact distinctGF12_coeff_table
  constructor
  · exact distinctGF12_coeff_0
  constructor
  · exact distinctGF12_coeff_6
  constructor
  · exact distinctGF12_coeff_12
  constructor
  · exact glaisher_roundtrip_odd_5_1
  constructor
  · exact glaisher_roundtrip_odd_3_3
  constructor
  · exact glaisher_roundtrip_odd_3_1_1_1
  constructor
  · exact glaisher_roundtrip_odd_six_ones
  constructor
  · exact glaisher_sum_odd_3_1_1_1
  · exact glaisher_sum_distinct_4_2

end BEDC.Derived.EulerDistinctOddPartition
