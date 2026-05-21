import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpeckerSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpeckerSequenceUp : Type where
  | mk
      (regularSource streamSchedule dyadicLedger monotoneLedger boundedLedger realSeal
        transportRows continuationRows provenance localName : BHist) :
      SpeckerSequenceUp
  deriving DecidableEq

def speckerSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: speckerSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: speckerSequenceEncodeBHist h

def speckerSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (speckerSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (speckerSequenceDecodeBHist tail)

private theorem SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, speckerSequenceDecodeBHist (speckerSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def speckerSequenceFields : SpeckerSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpeckerSequenceUp.mk regularSource streamSchedule dyadicLedger monotoneLedger boundedLedger
      realSeal transportRows continuationRows provenance localName =>
      [regularSource, streamSchedule, dyadicLedger, monotoneLedger, boundedLedger, realSeal,
        transportRows, continuationRows, provenance, localName]

def speckerSequenceToEventFlow : SpeckerSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (speckerSequenceFields x).map speckerSequenceEncodeBHist

private def SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault index rest

def speckerSequenceFromEventFlow (ef : EventFlow) : Option SpeckerSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SpeckerSequenceUp.mk
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (speckerSequenceDecodeBHist (SpeckerSequenceTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem SpeckerSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SpeckerSequenceUp,
      speckerSequenceFromEventFlow (speckerSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk regularSource streamSchedule dyadicLedger monotoneLedger boundedLedger realSeal
      transportRows continuationRows provenance localName =>
      change
        some
          (SpeckerSequenceUp.mk
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist regularSource))
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist streamSchedule))
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist dyadicLedger))
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist monotoneLedger))
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist boundedLedger))
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist realSeal))
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist transportRows))
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist continuationRows))
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist provenance))
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist localName))) =
          some
            (SpeckerSequenceUp.mk regularSource streamSchedule dyadicLedger monotoneLedger
              boundedLedger realSeal transportRows continuationRows provenance localName)
      rw [SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode regularSource,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode streamSchedule,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode dyadicLedger,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode monotoneLedger,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode boundedLedger,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode realSeal,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode transportRows,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode continuationRows,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode provenance,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode localName]

private theorem SpeckerSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SpeckerSequenceUp} :
    speckerSequenceToEventFlow x = speckerSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      speckerSequenceFromEventFlow (speckerSequenceToEventFlow x) =
        speckerSequenceFromEventFlow (speckerSequenceToEventFlow y) :=
    congrArg speckerSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SpeckerSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SpeckerSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance speckerSequenceBHistCarrier : BHistCarrier SpeckerSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := speckerSequenceToEventFlow
  fromEventFlow := speckerSequenceFromEventFlow

instance speckerSequenceChapterTasteGate : ChapterTasteGate SpeckerSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change speckerSequenceFromEventFlow (speckerSequenceToEventFlow x) = some x
    exact SpeckerSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SpeckerSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SpeckerSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, speckerSequenceDecodeBHist (speckerSequenceEncodeBHist h) = h) ∧
      (∀ x : SpeckerSequenceUp,
        speckerSequenceFromEventFlow (speckerSequenceToEventFlow x) = some x) ∧
        (∀ x y : SpeckerSequenceUp,
          speckerSequenceToEventFlow x = speckerSequenceToEventFlow y → x = y) ∧
          speckerSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact SpeckerSequenceTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact SpeckerSequenceTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact SpeckerSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.SpeckerSequenceUp
