import BEDC.Derived.SpeckerSequenceUp
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
        transportRows continuationRows provenance nameCert : BHist) :
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

private theorem SpeckerSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, speckerSequenceDecodeBHist (speckerSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def speckerSequenceFields : SpeckerSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpeckerSequenceUp.mk regularSource streamSchedule dyadicLedger monotoneLedger
      boundedLedger realSeal transportRows continuationRows provenance nameCert =>
      [regularSource, streamSchedule, dyadicLedger, monotoneLedger, boundedLedger, realSeal,
        transportRows, continuationRows, provenance, nameCert]

def speckerSequenceToEventFlow : SpeckerSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (speckerSequenceFields x).map speckerSequenceEncodeBHist

private def speckerSequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => speckerSequenceEventAtDefault index rest

def speckerSequenceFromEventFlow : EventFlow → Option SpeckerSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SpeckerSequenceUp.mk
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 0 ef))
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 1 ef))
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 2 ef))
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 3 ef))
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 4 ef))
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 5 ef))
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 6 ef))
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 7 ef))
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 8 ef))
        (speckerSequenceDecodeBHist (speckerSequenceEventAtDefault 9 ef)))

private theorem SpeckerSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SpeckerSequenceUp,
      speckerSequenceFromEventFlow (speckerSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk regularSource streamSchedule dyadicLedger monotoneLedger boundedLedger realSeal
      transportRows continuationRows provenance nameCert =>
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
            (speckerSequenceDecodeBHist (speckerSequenceEncodeBHist nameCert))) =
          some
            (SpeckerSequenceUp.mk regularSource streamSchedule dyadicLedger monotoneLedger
              boundedLedger realSeal transportRows continuationRows provenance nameCert)
      rw [SpeckerSequenceTasteGate_single_carrier_alignment_decode regularSource,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode streamSchedule,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode dyadicLedger,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode monotoneLedger,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode boundedLedger,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode realSeal,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode transportRows,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode continuationRows,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode provenance,
        SpeckerSequenceTasteGate_single_carrier_alignment_decode nameCert]

private theorem speckerSequenceToEventFlow_injective {x y : SpeckerSequenceUp} :
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

private theorem speckerSequence_field_faithful :
    ∀ x y : SpeckerSequenceUp, speckerSequenceFields x = speckerSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk regularSource₁ streamSchedule₁ dyadicLedger₁ monotoneLedger₁ boundedLedger₁ realSeal₁
      transportRows₁ continuationRows₁ provenance₁ nameCert₁ =>
      cases y with
      | mk regularSource₂ streamSchedule₂ dyadicLedger₂ monotoneLedger₂ boundedLedger₂ realSeal₂
          transportRows₂ continuationRows₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

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
    exact hxy (speckerSequenceToEventFlow_injective heq)

instance speckerSequenceFieldFaithful : FieldFaithful SpeckerSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := speckerSequenceFields
  field_faithful := speckerSequence_field_faithful

def taste_gate : ChapterTasteGate SpeckerSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  speckerSequenceChapterTasteGate

theorem SpeckerSequenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SpeckerSequenceUp) ∧
      Nonempty (ChapterTasteGate SpeckerSequenceUp) ∧
      Nonempty (FieldFaithful SpeckerSequenceUp) ∧
      (∀ h : BHist, speckerSequenceDecodeBHist (speckerSequenceEncodeBHist h) = h) ∧
      (∀ x : SpeckerSequenceUp,
        speckerSequenceFromEventFlow (speckerSequenceToEventFlow x) = some x) ∧
      (∀ x y : SpeckerSequenceUp,
        speckerSequenceToEventFlow x = speckerSequenceToEventFlow y → x = y) ∧
      speckerSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨speckerSequenceBHistCarrier⟩
  constructor
  · exact ⟨speckerSequenceChapterTasteGate⟩
  constructor
  · exact ⟨speckerSequenceFieldFaithful⟩
  constructor
  · exact SpeckerSequenceTasteGate_single_carrier_alignment_decode
  constructor
  · exact SpeckerSequenceTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact speckerSequenceToEventFlow_injective heq
  · rfl

end BEDC.Derived.SpeckerSequenceUp
