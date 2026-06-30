import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PartitionBasinUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PartitionBasinUp : Type where
  | mk (P M S D F I T H C Q N : BHist) : PartitionBasinUp
  deriving DecidableEq

def partitionBasinEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: partitionBasinEncodeBHist h
  | BHist.e1 h => BMark.b1 :: partitionBasinEncodeBHist h

def partitionBasinDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (partitionBasinDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (partitionBasinDecodeBHist tail)

private theorem PartitionBasinTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, partitionBasinDecodeBHist (partitionBasinEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def partitionBasinToEventFlow : PartitionBasinUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PartitionBasinUp.mk P M S D F I T H C Q N =>
      [partitionBasinEncodeBHist P,
        partitionBasinEncodeBHist M,
        partitionBasinEncodeBHist S,
        partitionBasinEncodeBHist D,
        partitionBasinEncodeBHist F,
        partitionBasinEncodeBHist I,
        partitionBasinEncodeBHist T,
        partitionBasinEncodeBHist H,
        partitionBasinEncodeBHist C,
        partitionBasinEncodeBHist Q,
        partitionBasinEncodeBHist N]

private def partitionBasinEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => partitionBasinEventAtDefault index rest

def partitionBasinFromEventFlow : EventFlow → Option PartitionBasinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (PartitionBasinUp.mk
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 0 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 1 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 2 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 3 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 4 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 5 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 6 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 7 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 8 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 9 ef))
        (partitionBasinDecodeBHist (partitionBasinEventAtDefault 10 ef)))

private theorem PartitionBasinTasteGate_single_carrier_alignment_round_trip
    (x : PartitionBasinUp) :
    partitionBasinFromEventFlow (partitionBasinToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P M S D F I T H C Q N =>
      change
        some
            (PartitionBasinUp.mk
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist P))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist M))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist S))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist D))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist F))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist I))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist T))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist H))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist C))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist Q))
              (partitionBasinDecodeBHist (partitionBasinEncodeBHist N))) =
          some (PartitionBasinUp.mk P M S D F I T H C Q N)
      rw [PartitionBasinTasteGate_single_carrier_alignment_decode_encode P,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode M,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode S,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode D,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode F,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode I,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode T,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode H,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode C,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode Q,
        PartitionBasinTasteGate_single_carrier_alignment_decode_encode N]

private theorem PartitionBasinTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PartitionBasinUp} :
    partitionBasinToEventFlow x = partitionBasinToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      partitionBasinFromEventFlow (partitionBasinToEventFlow x) =
        partitionBasinFromEventFlow (partitionBasinToEventFlow y) :=
    congrArg partitionBasinFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PartitionBasinTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PartitionBasinTasteGate_single_carrier_alignment_round_trip y)))

instance partitionBasinBHistCarrier : BHistCarrier PartitionBasinUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := partitionBasinToEventFlow
  fromEventFlow := partitionBasinFromEventFlow

instance partitionBasinChapterTasteGate : ChapterTasteGate PartitionBasinUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change partitionBasinFromEventFlow (partitionBasinToEventFlow x) = some x
    exact PartitionBasinTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PartitionBasinTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PartitionBasinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  partitionBasinChapterTasteGate

theorem PartitionBasinTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier PartitionBasinUp,
      Nonempty (@ChapterTasteGate PartitionBasinUp carrier)) ∧
      (∀ h : BHist, partitionBasinDecodeBHist (partitionBasinEncodeBHist h) = h) ∧
        (∀ x : PartitionBasinUp,
          partitionBasinFromEventFlow (partitionBasinToEventFlow x) = some x) ∧
          partitionBasinEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨partitionBasinBHistCarrier, ⟨partitionBasinChapterTasteGate⟩⟩,
      PartitionBasinTasteGate_single_carrier_alignment_decode_encode,
      PartitionBasinTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.PartitionBasinUp
