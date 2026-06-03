import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PartitionOfUnityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PartitionOfUnityUp : Type where
  | mk (T L Q R W F S H C P N : BHist) : PartitionOfUnityUp
  deriving DecidableEq

def partitionOfUnityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: partitionOfUnityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: partitionOfUnityEncodeBHist h

def partitionOfUnityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (partitionOfUnityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (partitionOfUnityDecodeBHist tail)

private theorem PartitionOfUnityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def partitionOfUnityFields : PartitionOfUnityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PartitionOfUnityUp.mk T L Q R W F S H C P N => [T, L, Q, R, W, F, S, H, C, P, N]

def partitionOfUnityToEventFlow : PartitionOfUnityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (partitionOfUnityFields x).map partitionOfUnityEncodeBHist

private def partitionOfUnityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => partitionOfUnityRawAt index rest

def partitionOfUnityFromEventFlow (flow : EventFlow) : Option PartitionOfUnityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PartitionOfUnityUp.mk
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 0 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 1 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 2 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 3 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 4 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 5 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 6 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 7 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 8 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 9 flow))
      (partitionOfUnityDecodeBHist (partitionOfUnityRawAt 10 flow)))

private theorem PartitionOfUnityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PartitionOfUnityUp,
      partitionOfUnityFromEventFlow (partitionOfUnityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk T L Q R W F S H C P N =>
      change
        some
          (PartitionOfUnityUp.mk
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist T))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist L))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist Q))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist R))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist W))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist F))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist S))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist H))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist C))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist P))
            (partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist N))) =
          some (PartitionOfUnityUp.mk T L Q R W F S H C P N)
      rw [PartitionOfUnityTasteGate_single_carrier_alignment_decode T,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode L,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode Q,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode R,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode W,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode F,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode S,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode H,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode C,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode P,
        PartitionOfUnityTasteGate_single_carrier_alignment_decode N]

private theorem PartitionOfUnityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PartitionOfUnityUp} :
    partitionOfUnityToEventFlow x = partitionOfUnityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      partitionOfUnityFromEventFlow (partitionOfUnityToEventFlow x) =
        partitionOfUnityFromEventFlow (partitionOfUnityToEventFlow y) :=
    congrArg partitionOfUnityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PartitionOfUnityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PartitionOfUnityTasteGate_single_carrier_alignment_round_trip y)))

instance partitionOfUnityBHistCarrier : BHistCarrier PartitionOfUnityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := partitionOfUnityToEventFlow
  fromEventFlow := partitionOfUnityFromEventFlow

instance partitionOfUnityChapterTasteGate : ChapterTasteGate PartitionOfUnityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change partitionOfUnityFromEventFlow (partitionOfUnityToEventFlow x) = some x
    exact PartitionOfUnityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PartitionOfUnityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PartitionOfUnityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  partitionOfUnityChapterTasteGate

theorem PartitionOfUnityTasteGate_single_carrier_alignment :
    (∀ h : BHist, partitionOfUnityDecodeBHist (partitionOfUnityEncodeBHist h) = h) ∧
      (∀ x : PartitionOfUnityUp,
        partitionOfUnityFromEventFlow (partitionOfUnityToEventFlow x) = some x) ∧
        (∀ x y : PartitionOfUnityUp,
          partitionOfUnityToEventFlow x = partitionOfUnityToEventFlow y → x = y) ∧
          partitionOfUnityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PartitionOfUnityTasteGate_single_carrier_alignment_decode,
      PartitionOfUnityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        PartitionOfUnityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PartitionOfUnityUp
