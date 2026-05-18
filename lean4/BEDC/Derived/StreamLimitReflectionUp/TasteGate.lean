import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamLimitReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamLimitReflectionUp : Type where
  | mk :
      (schedule regularity realSeal code boundary transport route provenance name : BHist) →
      StreamLimitReflectionUp
  deriving DecidableEq

def streamLimitReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamLimitReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamLimitReflectionEncodeBHist h

def streamLimitReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamLimitReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamLimitReflectionDecodeBHist tail)

private theorem StreamLimitReflectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def streamLimitReflectionToEventFlow : StreamLimitReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StreamLimitReflectionUp.mk schedule regularity realSeal code boundary transport route
      provenance name =>
      [[BMark.b0],
        streamLimitReflectionEncodeBHist schedule,
        [BMark.b1, BMark.b0],
        streamLimitReflectionEncodeBHist regularity,
        [BMark.b1, BMark.b1, BMark.b0],
        streamLimitReflectionEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        streamLimitReflectionEncodeBHist code,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        streamLimitReflectionEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        streamLimitReflectionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        streamLimitReflectionEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        streamLimitReflectionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        streamLimitReflectionEncodeBHist name]

private def streamLimitReflectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => streamLimitReflectionEventAtDefault index rest

def streamLimitReflectionFromEventFlow (ef : EventFlow) : Option StreamLimitReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StreamLimitReflectionUp.mk
      (streamLimitReflectionDecodeBHist (streamLimitReflectionEventAtDefault 1 ef))
      (streamLimitReflectionDecodeBHist (streamLimitReflectionEventAtDefault 3 ef))
      (streamLimitReflectionDecodeBHist (streamLimitReflectionEventAtDefault 5 ef))
      (streamLimitReflectionDecodeBHist (streamLimitReflectionEventAtDefault 7 ef))
      (streamLimitReflectionDecodeBHist (streamLimitReflectionEventAtDefault 9 ef))
      (streamLimitReflectionDecodeBHist (streamLimitReflectionEventAtDefault 11 ef))
      (streamLimitReflectionDecodeBHist (streamLimitReflectionEventAtDefault 13 ef))
      (streamLimitReflectionDecodeBHist (streamLimitReflectionEventAtDefault 15 ef))
      (streamLimitReflectionDecodeBHist (streamLimitReflectionEventAtDefault 17 ef)))

private theorem StreamLimitReflectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StreamLimitReflectionUp,
      streamLimitReflectionFromEventFlow (streamLimitReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk schedule regularity realSeal code boundary transport route provenance name =>
      change
        some
          (StreamLimitReflectionUp.mk
            (streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist schedule))
            (streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist regularity))
            (streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist realSeal))
            (streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist code))
            (streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist boundary))
            (streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist transport))
            (streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist route))
            (streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist provenance))
            (streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist name))) =
          some
            (StreamLimitReflectionUp.mk schedule regularity realSeal code boundary transport
              route provenance name)
      rw [StreamLimitReflectionTasteGate_single_carrier_alignment_decode schedule,
        StreamLimitReflectionTasteGate_single_carrier_alignment_decode regularity,
        StreamLimitReflectionTasteGate_single_carrier_alignment_decode realSeal,
        StreamLimitReflectionTasteGate_single_carrier_alignment_decode code,
        StreamLimitReflectionTasteGate_single_carrier_alignment_decode boundary,
        StreamLimitReflectionTasteGate_single_carrier_alignment_decode transport,
        StreamLimitReflectionTasteGate_single_carrier_alignment_decode route,
        StreamLimitReflectionTasteGate_single_carrier_alignment_decode provenance,
        StreamLimitReflectionTasteGate_single_carrier_alignment_decode name]

private theorem StreamLimitReflectionToEventFlow_injective
    {x y : StreamLimitReflectionUp} :
    streamLimitReflectionToEventFlow x = streamLimitReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      streamLimitReflectionFromEventFlow (streamLimitReflectionToEventFlow x) =
        streamLimitReflectionFromEventFlow (streamLimitReflectionToEventFlow y) :=
    congrArg streamLimitReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StreamLimitReflectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StreamLimitReflectionTasteGate_single_carrier_alignment_round_trip y)))

private def streamLimitReflectionFields : StreamLimitReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StreamLimitReflectionUp.mk schedule regularity realSeal code boundary transport route
      provenance name =>
      [schedule, regularity, realSeal, code, boundary, transport, route, provenance, name]

private theorem StreamLimitReflectionTasteGate_single_carrier_alignment_fields :
    ∀ x y : StreamLimitReflectionUp,
      streamLimitReflectionFields x = streamLimitReflectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk schedule regularity realSeal code boundary transport route provenance name =>
      cases y with
      | mk schedule' regularity' realSeal' code' boundary' transport' route' provenance'
          name' =>
          cases hfields
          rfl

instance streamLimitReflectionBHistCarrier : BHistCarrier StreamLimitReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamLimitReflectionToEventFlow
  fromEventFlow := streamLimitReflectionFromEventFlow

instance streamLimitReflectionChapterTasteGate :
    ChapterTasteGate StreamLimitReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamLimitReflectionFromEventFlow (streamLimitReflectionToEventFlow x) = some x
    exact StreamLimitReflectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StreamLimitReflectionToEventFlow_injective heq)

instance streamLimitReflectionFieldFaithful : FieldFaithful StreamLimitReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := streamLimitReflectionFields
  field_faithful := StreamLimitReflectionTasteGate_single_carrier_alignment_fields

instance streamLimitReflectionNontrivial : Nontrivial StreamLimitReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StreamLimitReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StreamLimitReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StreamLimitReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  streamLimitReflectionChapterTasteGate

theorem StreamLimitReflectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      streamLimitReflectionDecodeBHist (streamLimitReflectionEncodeBHist h) = h) ∧
      (∀ x : StreamLimitReflectionUp,
        streamLimitReflectionFromEventFlow (streamLimitReflectionToEventFlow x) = some x) ∧
        (∀ x y : StreamLimitReflectionUp,
          streamLimitReflectionToEventFlow x = streamLimitReflectionToEventFlow y → x = y) ∧
          streamLimitReflectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨StreamLimitReflectionTasteGate_single_carrier_alignment_decode,
      StreamLimitReflectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => StreamLimitReflectionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.StreamLimitReflectionUp
