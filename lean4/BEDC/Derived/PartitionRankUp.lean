import BEDC.Derived.PartitionIdentitiesUp
import BEDC.Derived.RamanujanCongruenceUp

namespace BEDC.Derived.PartitionRankUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.PartitionIdentitiesUp
open BEDC.Derived.RamanujanCongruenceUp

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

private abbrev integerRing :
    BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def integerUpOfNat (n : Nat) : IntegerUp :=
  BEDC.Derived.RationalUp.intOfNat (natToUnary n) (natToUnary_unary n)

def maxNat (a b : Nat) : Nat :=
  if a <= b then b else a

def largestPart : List Nat -> Nat
  | [] => 0
  | part :: rest => maxNat part (largestPart rest)

def partCount (parts : List Nat) : Nat :=
  parts.length

-- Dyson rank: 最大部件减去部件数, 结果落在 BEDC 整数载体中。
def partitionRankInteger (parts : List Nat) : IntegerUp :=
  integerRing.sub (integerUpOfNat (largestPart parts)) (integerUpOfNat (partCount parts))

def negativeResidueNat (modulus residue : Nat) : Nat :=
  if residue = 0 then 0 else modulus - residue

def signedDifferenceResidue (modulus largest count : Nat) : Nat :=
  if modulus = 0 then
    0
  else if count <= largest then
    (largest - count) % modulus
  else
    negativeResidueNat modulus ((count - largest) % modulus)

def partitionRankResidue (modulus : Nat) (parts : List Nat) : Nat :=
  signedDifferenceResidue modulus (largestPart parts) (partCount parts)

def encodedRankCodeResidueUp (modulus rankCode : BHist) : BHist :=
  BEDC.Derived.PadicUp.natModFn modulus rankCode

def rankResidueCount (modulus n residue : Nat) : Nat :=
  countWhere (fun parts => partitionRankResidue modulus parts == residue) (partitionLists n)

def rankGeneratingResidueRow (modulus n : Nat) : List Nat :=
  (List.range modulus).map (rankResidueCount modulus n)

def rankResidueCountModFive (n residue : Nat) : Nat :=
  rankResidueCount 5 n residue

def rankGeneratingRowModFive (n : Nat) : List Nat :=
  rankGeneratingResidueRow 5 n

def dysonRankModFiveEquidistributedAt (n : Nat) : Prop :=
  ∃ common : Nat,
    rankResidueCountModFive (ramanujanP5Index n) 0 = common ∧
      rankResidueCountModFive (ramanujanP5Index n) 1 = common ∧
        rankResidueCountModFive (ramanujanP5Index n) 2 = common ∧
          rankResidueCountModFive (ramanujanP5Index n) 3 = common ∧
            rankResidueCountModFive (ramanujanP5Index n) 4 = common

def rankModFiveResidueCountsTotalAt (n : Nat) : Prop :=
  ∀ common : Nat,
    rankResidueCountModFive (ramanujanP5Index n) 0 = common ->
      rankResidueCountModFive (ramanujanP5Index n) 1 = common ->
        rankResidueCountModFive (ramanujanP5Index n) 2 = common ->
          rankResidueCountModFive (ramanujanP5Index n) 3 = common ->
            rankResidueCountModFive (ramanujanP5Index n) 4 = common ->
              PartitionNumber (ramanujanP5Index n) = 5 * common

theorem partitionRankInteger_self_rel (parts : List Nat) :
    IntEq (partitionRankInteger parts)
      (integerRing.sub (integerUpOfNat (largestPart parts))
        (integerUpOfNat (partCount parts))) := by
  exact integerRing.refl _

theorem largestPart_empty :
    largestPart [] = 0 := by
  rfl

theorem largestPart_singleton (n : Nat) :
    largestPart [n] = n := by
  unfold largestPart maxNat
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

theorem partCount_empty :
    partCount [] = 0 := by
  rfl

theorem partCount_singleton (n : Nat) :
    partCount [n] = 1 := by
  rfl

theorem partitionRankResidue_empty_mod_five :
    partitionRankResidue 5 [] = 0 := by
  rfl

theorem partitionRankResidue_four_singleton_mod_five :
    partitionRankResidue 5 [4] = 3 := by
  rfl

theorem partitionRankResidue_four_all_ones_mod_five :
    partitionRankResidue 5 [1, 1, 1, 1] = 2 := by
  rfl

theorem partitionRankResidue_two_two_mod_five :
    partitionRankResidue 5 [2, 2] = 0 := by
  rfl

theorem encodedRankCodeResidueUp_divrem (modulus rankCode : BHist)
    (modulusUnary : UnaryHistory modulus)
    (rankCodeUnary : UnaryHistory rankCode)
    (modulusNonempty : hsame modulus BHist.Empty -> False) :
    BEDC.Derived.PrimeUp.NatDivRem modulus rankCode
      (BEDC.Derived.PadicUp.natQuotFn modulus rankCode)
      (encodedRankCodeResidueUp modulus rankCode) := by
  unfold encodedRankCodeResidueUp
  exact BEDC.Derived.PadicUp.natModFn_spec modulusUnary rankCodeUnary modulusNonempty

theorem rankGeneratingRowModFive_four :
    rankGeneratingRowModFive 4 = [1, 1, 1, 1, 1] := by
  rfl

theorem rankResidueCounts_mod_five_four :
    rankResidueCountModFive 4 0 = 1 ∧
      rankResidueCountModFive 4 1 = 1 ∧
        rankResidueCountModFive 4 2 = 1 ∧
          rankResidueCountModFive 4 3 = 1 ∧
            rankResidueCountModFive 4 4 = 1 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl

theorem dysonRankModFiveEquidistributedAt_zero :
    dysonRankModFiveEquidistributedAt 0 := by
  unfold dysonRankModFiveEquidistributedAt
  exact ⟨1, by rfl, by rfl, by rfl, by rfl, by rfl⟩

theorem rankModFiveResidueCountsTotalAt_zero :
    rankModFiveResidueCountsTotalAt 0 := by
  unfold rankModFiveResidueCountsTotalAt
  intro common h0 _h1 _h2 _h3 _h4
  rw [← h0]
  rfl

theorem rankGeneratingRowModFive_nine :
    rankGeneratingRowModFive 9 = [6, 6, 6, 6, 6] := by
  rfl

theorem dysonRankModFiveEquidistributedAt_one :
    dysonRankModFiveEquidistributedAt 1 := by
  unfold dysonRankModFiveEquidistributedAt
  exact ⟨6, by rfl, by rfl, by rfl, by rfl, by rfl⟩

theorem rankModFiveResidueCountsTotalAt_one :
    rankModFiveResidueCountsTotalAt 1 := by
  unfold rankModFiveResidueCountsTotalAt
  intro common h0 _h1 _h2 _h3 _h4
  rw [← h0]
  rfl

theorem dysonRankModFiveBridge_supplies_fivefold_count
    (n : Nat) :
    dysonRankModFiveEquidistributedAt n ->
      rankModFiveResidueCountsTotalAt n ->
        ∃ common : Nat, PartitionNumber (ramanujanP5Index n) = 5 * common := by
  intro equidistribution
  intro total
  unfold dysonRankModFiveEquidistributedAt at equidistribution
  cases equidistribution with
  | intro common data =>
      exact ⟨common, total common data.left data.right.left data.right.right.left
        data.right.right.right.left data.right.right.right.right⟩

theorem partitionRankRamanujanP5_small_values :
    ramanujanP5CongruentAt 0 ∧ ramanujanP5CongruentAt 1 := by
  constructor
  · exact ramanujan_p5_at_zero
  · exact ramanujan_p5_at_one

theorem partitionRank_constructive_export :
    partitionRankResidue 5 [] = 0 ∧
      partitionRankResidue 5 [4] = 3 ∧
        rankGeneratingRowModFive 4 = [1, 1, 1, 1, 1] ∧
          dysonRankModFiveEquidistributedAt 0 ∧
            rankModFiveResidueCountsTotalAt 0 ∧
              (∃ common : Nat, PartitionNumber (ramanujanP5Index 0) = 5 * common) ∧
                ramanujanP5CongruentAt 0 := by
  constructor
  · exact partitionRankResidue_empty_mod_five
  · constructor
    · exact partitionRankResidue_four_singleton_mod_five
    · constructor
      · exact rankGeneratingRowModFive_four
      · constructor
        · exact dysonRankModFiveEquidistributedAt_zero
        · constructor
          · exact rankModFiveResidueCountsTotalAt_zero
          · constructor
            · exact dysonRankModFiveBridge_supplies_fivefold_count 0
                dysonRankModFiveEquidistributedAt_zero
                rankModFiveResidueCountsTotalAt_zero
            · exact ramanujan_p5_at_zero

end BEDC.Derived.PartitionRankUp
