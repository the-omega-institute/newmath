import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SummableSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SummableSequenceUp : Type where
  | mk :
      (realSeriesSource partialSumWindow cauchyTailBudget convergenceHandoff readback
        streamObservation realSeal transport replay provenance localName : BHist) →
      SummableSequenceUp
  deriving DecidableEq

def summableSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: summableSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: summableSequenceEncodeBHist h

def summableSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (summableSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (summableSequenceDecodeBHist tail)

theorem SummableSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, summableSequenceDecodeBHist (summableSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def summableSequenceFields : SummableSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SummableSequenceUp.mk realSeriesSource partialSumWindow cauchyTailBudget
      convergenceHandoff readback streamObservation realSeal transport replay provenance localName =>
      [realSeriesSource, partialSumWindow, cauchyTailBudget, convergenceHandoff, readback,
        streamObservation, realSeal, transport, replay, provenance, localName]

def summableSequenceToEventFlow : SummableSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map summableSequenceEncodeBHist (summableSequenceFields x)

private def SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault index rest

def summableSequenceFromEventFlow : EventFlow → Option SummableSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SummableSequenceUp.mk
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
        (summableSequenceDecodeBHist
          (SummableSequenceTasteGate_single_carrier_alignment_eventAtDefault 10 ef)))

theorem SummableSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SummableSequenceUp,
      summableSequenceFromEventFlow (summableSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk realSeriesSource partialSumWindow cauchyTailBudget convergenceHandoff readback
      streamObservation realSeal transport replay provenance localName =>
      change
        some
          (SummableSequenceUp.mk
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist realSeriesSource))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist partialSumWindow))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist cauchyTailBudget))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist convergenceHandoff))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist readback))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist streamObservation))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist realSeal))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist transport))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist replay))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist provenance))
            (summableSequenceDecodeBHist (summableSequenceEncodeBHist localName))) =
          some
            (SummableSequenceUp.mk realSeriesSource partialSumWindow cauchyTailBudget
              convergenceHandoff readback streamObservation realSeal transport replay provenance
              localName)
      rw [SummableSequenceTasteGate_single_carrier_alignment_decode_encode realSeriesSource,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode partialSumWindow,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode cauchyTailBudget,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode convergenceHandoff,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode readback,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode streamObservation,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode realSeal,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode transport,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode replay,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode provenance,
        SummableSequenceTasteGate_single_carrier_alignment_decode_encode localName]

theorem SummableSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SummableSequenceUp} :
    summableSequenceToEventFlow x = summableSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      summableSequenceFromEventFlow (summableSequenceToEventFlow x) =
        summableSequenceFromEventFlow (summableSequenceToEventFlow y) :=
    congrArg summableSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SummableSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SummableSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem SummableSequenceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : SummableSequenceUp, summableSequenceFields x = summableSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk realSeriesSource₁ partialSumWindow₁ cauchyTailBudget₁ convergenceHandoff₁ readback₁
      streamObservation₁ realSeal₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk realSeriesSource₂ partialSumWindow₂ cauchyTailBudget₂ convergenceHandoff₂ readback₂
          streamObservation₂ realSeal₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases h
          rfl

instance summableSequenceBHistCarrier : BHistCarrier SummableSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := summableSequenceToEventFlow
  fromEventFlow := summableSequenceFromEventFlow

instance summableSequenceChapterTasteGate : ChapterTasteGate SummableSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change summableSequenceFromEventFlow (summableSequenceToEventFlow x) = some x
    exact SummableSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SummableSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance summableSequenceFieldFaithful : FieldFaithful SummableSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := summableSequenceFields
  field_faithful := SummableSequenceTasteGate_single_carrier_alignment_field_faithful

instance summableSequenceNontrivial : Nontrivial SummableSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SummableSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SummableSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SummableSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  summableSequenceChapterTasteGate

theorem SummableSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, summableSequenceDecodeBHist (summableSequenceEncodeBHist h) = h) ∧
      (∀ x : SummableSequenceUp,
        summableSequenceFromEventFlow (summableSequenceToEventFlow x) = some x) ∧
      (∀ x y : SummableSequenceUp,
        summableSequenceToEventFlow x = summableSequenceToEventFlow y → x = y) ∧
      summableSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SummableSequenceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact SummableSequenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact SummableSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.SummableSequenceUp
