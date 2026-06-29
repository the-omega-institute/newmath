import BEDC.Derived.ThueMorseUp

namespace BEDC.Derived.ThueSequenceUp

open BEDC.Derived.ThueMorseUp

def thuePrefixFour : BWord :=
  thueMorsePrefix 2

def thuePrefixEight : BWord :=
  thueMorsePrefix 3

def wordEqBool : BWord -> BWord -> Bool
  | [], [] => true
  | x :: xs, y :: ys => Bit.eqBool x y && wordEqBool xs ys
  | [], _ :: _ => false
  | _ :: _, [] => false

def containsWord (needle : BWord) : List BWord -> Bool
  | [] => false
  | word :: rest => wordEqBool needle word || containsWord needle rest

def appendUniqueWord (word : BWord) (seen : List BWord) : List BWord :=
  if containsWord word seen then seen else seen ++ [word]

def uniqueWordsFrom : List BWord -> List BWord -> List BWord
  | seen, [] => seen
  | seen, word :: rest => uniqueWordsFrom (appendUniqueWord word seen) rest

def uniqueWords (words : List BWord) : List BWord :=
  uniqueWordsFrom [] words

def factorWindow (size start : Nat) (word : BWord) : BWord :=
  (word.drop start).take size

def factorsOfLengthFrom (size start : Nat) : Nat -> BWord -> List BWord
  | 0, _word => []
  | Nat.succ fuel, word =>
      let window := factorWindow size start word
      if window.length == size then
        window :: factorsOfLengthFrom size (Nat.succ start) fuel word
      else
        []

def factorsOfLength (size fuel : Nat) (word : BWord) : List BWord :=
  factorsOfLengthFrom size 0 fuel word

def subwordComplexity (size fuel : Nat) (word : BWord) : Nat :=
  (uniqueWords (factorsOfLength size fuel word)).length

def binaryWordsOfLength : Nat -> List BWord
  | 0 => [[]]
  | Nat.succ n =>
      (binaryWordsOfLength n).map (fun word => Bit.zero :: word) ++
        (binaryWordsOfLength n).map (fun word => Bit.one :: word)

def binaryWordsUpTo : Nat -> List BWord
  | 0 => [[]]
  | Nat.succ n => binaryWordsUpTo n ++ binaryWordsOfLength (Nat.succ n)

def positiveBinaryWordsUpTo : Nat -> List BWord
  | 0 => []
  | Nat.succ n => positiveBinaryWordsUpTo n ++ binaryWordsOfLength (Nat.succ n)

def containsFactorFrom (needle word : BWord) (start : Nat) : Nat -> Bool
  | 0 => false
  | Nat.succ fuel =>
      wordEqBool needle (factorWindow needle.length start word) ||
        containsFactorFrom needle word (Nat.succ start) fuel

def containsFactor (needle word : BWord) : Bool :=
  containsFactorFrom needle word 0 (Nat.succ word.length)

def overlapWord (a : Bit) (middle : BWord) : BWord :=
  [a] ++ middle ++ [a] ++ middle ++ [a]

def cubeWord (block : BWord) : BWord :=
  block ++ block ++ block

def overlapCandidates (middleFuel : Nat) : List BWord :=
  (binaryWordsUpTo middleFuel).flatMap
    (fun middle => [overlapWord Bit.zero middle, overlapWord Bit.one middle])

def cubeCandidates (blockFuel : Nat) : List BWord :=
  (positiveBinaryWordsUpTo blockFuel).map cubeWord

def containsAnyFactor (candidates : List BWord) (word : BWord) : Bool :=
  match candidates with
  | [] => false
  | candidate :: rest => containsFactor candidate word || containsAnyFactor rest word

def hasOverlapWithMiddleFuel (middleFuel : Nat) (word : BWord) : Bool :=
  containsAnyFactor (overlapCandidates middleFuel) word

def hasCubeWithBlockFuel (blockFuel : Nat) (word : BWord) : Bool :=
  containsAnyFactor (cubeCandidates blockFuel) word

def FuelOverlapFree (middleFuel : Nat) (word : BWord) : Prop :=
  hasOverlapWithMiddleFuel middleFuel word = false

def FuelCubeFree (blockFuel : Nat) (word : BWord) : Prop :=
  hasCubeWithBlockFuel blockFuel word = false

theorem thuePrefixFour_shape :
    thuePrefixFour = [Bit.zero, Bit.one, Bit.one, Bit.zero] := by
  rfl

theorem thuePrefixFour_fuel_overlap_free :
    FuelOverlapFree 1 thuePrefixFour := by
  rfl

theorem thuePrefixFour_fuel_cube_free :
    FuelCubeFree 1 thuePrefixFour := by
  rfl

theorem thuePrefixEight_length_two_factor_list :
    factorsOfLength 2 8 thuePrefixEight =
      [[Bit.zero, Bit.one], [Bit.one, Bit.one], [Bit.one, Bit.zero],
        [Bit.zero, Bit.one], [Bit.one, Bit.zero], [Bit.zero, Bit.zero],
        [Bit.zero, Bit.one]] := by
  rfl

theorem thuePrefixEight_length_two_unique_factors :
    uniqueWords (factorsOfLength 2 8 thuePrefixEight) =
      [[Bit.zero, Bit.one], [Bit.one, Bit.one], [Bit.one, Bit.zero],
        [Bit.zero, Bit.zero]] := by
  rfl

theorem thuePrefixEight_length_two_complexity :
    subwordComplexity 2 8 thuePrefixEight = 4 := by
  rfl

theorem thuePrefixFour_partition_indices :
    indicesOfSymbol Bit.zero thuePrefixFour = [0, 3] /\
      indicesOfSymbol Bit.one thuePrefixFour = [1, 2] := by
  constructor
  · rfl
  · rfl

theorem thuePrefixFour_prouhet_order_one_partition :
    natListPowerSum 0 (indicesOfSymbol Bit.zero thuePrefixFour) =
        natListPowerSum 0 (indicesOfSymbol Bit.one thuePrefixFour) /\
      natListPowerSum 1 (indicesOfSymbol Bit.zero thuePrefixFour) =
        natListPowerSum 1 (indicesOfSymbol Bit.one thuePrefixFour) := by
  exact thueMorse_pte_level_two_order_one

theorem thuePrefixFour_finite_sequence_export :
    FuelOverlapFree 1 thuePrefixFour /\
      FuelCubeFree 1 thuePrefixFour /\
      subwordComplexity 2 8 thuePrefixEight = 4 /\
      natListPowerSum 0 (indicesOfSymbol Bit.zero thuePrefixFour) =
          natListPowerSum 0 (indicesOfSymbol Bit.one thuePrefixFour) /\
      natListPowerSum 1 (indicesOfSymbol Bit.zero thuePrefixFour) =
          natListPowerSum 1 (indicesOfSymbol Bit.one thuePrefixFour) := by
  constructor
  · exact thuePrefixFour_fuel_overlap_free
  · constructor
    · exact thuePrefixFour_fuel_cube_free
    · constructor
      · exact thuePrefixEight_length_two_complexity
      · exact thuePrefixFour_prouhet_order_one_partition

end BEDC.Derived.ThueSequenceUp
