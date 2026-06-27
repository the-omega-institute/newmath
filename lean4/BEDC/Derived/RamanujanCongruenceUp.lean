import BEDC.Derived.PartitionIdentitiesUp
import BEDC.Derived.PartitionUp
import BEDC.Derived.ZModUp

namespace BEDC.Derived.RamanujanCongruenceUp

open BEDC.FKernel.Hist
open BEDC.Derived.IntUp (natToUnary)

abbrev PartitionNumber (n : Nat) : Nat :=
  BEDC.Derived.PartitionUp.partitionNumber n

def partitionResidue (modulus n : Nat) : Nat :=
  PartitionNumber n % modulus

def ramanujanP5Index (n : Nat) : Nat :=
  5 * n + 4

def ramanujanP7Index (n : Nat) : Nat :=
  7 * n + 5

def ramanujanP5CongruentAt (n : Nat) : Prop :=
  partitionResidue 5 (ramanujanP5Index n) = 0

def ramanujanP7CongruentAt (n : Nat) : Prop :=
  partitionResidue 7 (ramanujanP7Index n) = 0

abbrev NatFiveHist : BHist :=
  natToUnary 5

abbrev NatSevenHist : BHist :=
  natToUnary 7

def partitionNumberHist (n : Nat) : BHist :=
  natToUnary (PartitionNumber n)

def partitionResidueHist (modulus index : Nat) : BHist :=
  BEDC.Derived.PadicUp.natModFn (natToUnary modulus)
    (partitionNumberHist index)

theorem partitionNumber_four_exact :
    PartitionNumber 4 = 5 := by
  exact BEDC.Derived.PartitionUp.partitionNumber_four

theorem partitionNumber_five_exact :
    PartitionNumber 5 = 7 := by
  exact BEDC.Derived.PartitionUp.partitionNumber_five

theorem partitionNumber_nine_exact :
    PartitionNumber 9 = 30 := by
  rfl

theorem partitionNumber_twelve_exact :
    PartitionNumber 12 = 77 := by
  rfl

theorem partitionNumber_fourteen_exact :
    PartitionNumber 14 = 135 := by
  rfl

theorem partitionNumber_nineteen_exact :
    PartitionNumber 19 = 490 := by
  rfl

theorem ramanujan_p5_at_zero :
    ramanujanP5CongruentAt 0 := by
  rfl

theorem ramanujan_p5_at_one :
    ramanujanP5CongruentAt 1 := by
  rfl

theorem ramanujan_p5_at_two :
    ramanujanP5CongruentAt 2 := by
  rfl

theorem ramanujan_p5_at_three :
    ramanujanP5CongruentAt 3 := by
  rfl

theorem ramanujan_p5_small_values :
    ramanujanP5CongruentAt 0 ∧
      ramanujanP5CongruentAt 1 ∧
      ramanujanP5CongruentAt 2 ∧
      ramanujanP5CongruentAt 3 := by
  constructor
  · exact ramanujan_p5_at_zero
  · constructor
    · exact ramanujan_p5_at_one
    · constructor
      · exact ramanujan_p5_at_two
      · exact ramanujan_p5_at_three

theorem ramanujan_p7_at_zero :
    ramanujanP7CongruentAt 0 := by
  rfl

theorem ramanujan_p7_at_one :
    ramanujanP7CongruentAt 1 := by
  rfl

theorem ramanujan_p7_at_two :
    ramanujanP7CongruentAt 2 := by
  rfl

theorem ramanujan_p7_small_values :
    ramanujanP7CongruentAt 0 ∧
      ramanujanP7CongruentAt 1 ∧
      ramanujanP7CongruentAt 2 := by
  constructor
  · exact ramanujan_p7_at_zero
  · constructor
    · exact ramanujan_p7_at_one
    · exact ramanujan_p7_at_two

theorem ramanujan_p5_hist_at_zero :
    hsame (partitionResidueHist 5 (ramanujanP5Index 0)) BHist.Empty := by
  rfl

theorem ramanujan_p7_hist_at_zero :
    hsame (partitionResidueHist 7 (ramanujanP7Index 0)) BHist.Empty := by
  rfl

end BEDC.Derived.RamanujanCongruenceUp
