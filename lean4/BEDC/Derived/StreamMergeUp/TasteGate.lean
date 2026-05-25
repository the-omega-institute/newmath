import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamMergeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamMergeUp : Type where
  | mk
      (sourceLeft sourceRight selector leftWindow rightWindow mergedWindow transport
        continuation provenance localName : BHist) :
      StreamMergeUp
  deriving DecidableEq

def streamMergeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamMergeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamMergeEncodeBHist h

def streamMergeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamMergeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamMergeDecodeBHist tail)

private theorem StreamMergeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, streamMergeDecodeBHist (streamMergeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def streamMergeFields : StreamMergeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StreamMergeUp.mk sourceLeft sourceRight selector leftWindow rightWindow mergedWindow
      transport continuation provenance localName =>
      [sourceLeft, sourceRight, selector, leftWindow, rightWindow, mergedWindow, transport,
        continuation, provenance, localName]

def streamMergeToEventFlow : StreamMergeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StreamMergeUp.mk sourceLeft sourceRight selector leftWindow rightWindow mergedWindow
      transport continuation provenance localName =>
      [streamMergeEncodeBHist sourceLeft,
        streamMergeEncodeBHist sourceRight,
        streamMergeEncodeBHist selector,
        streamMergeEncodeBHist leftWindow,
        streamMergeEncodeBHist rightWindow,
        streamMergeEncodeBHist mergedWindow,
        streamMergeEncodeBHist transport,
        streamMergeEncodeBHist continuation,
        streamMergeEncodeBHist provenance,
        streamMergeEncodeBHist localName]

private def StreamMergeTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      StreamMergeTasteGate_single_carrier_alignment_eventAtDefault index rest

def streamMergeFromEventFlow (ef : EventFlow) : Option StreamMergeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StreamMergeUp.mk
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (streamMergeDecodeBHist
        (StreamMergeTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem StreamMergeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StreamMergeUp, streamMergeFromEventFlow (streamMergeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight selector leftWindow rightWindow mergedWindow transport
      continuation provenance localName =>
      change
        some
          (StreamMergeUp.mk
            (streamMergeDecodeBHist (streamMergeEncodeBHist sourceLeft))
            (streamMergeDecodeBHist (streamMergeEncodeBHist sourceRight))
            (streamMergeDecodeBHist (streamMergeEncodeBHist selector))
            (streamMergeDecodeBHist (streamMergeEncodeBHist leftWindow))
            (streamMergeDecodeBHist (streamMergeEncodeBHist rightWindow))
            (streamMergeDecodeBHist (streamMergeEncodeBHist mergedWindow))
            (streamMergeDecodeBHist (streamMergeEncodeBHist transport))
            (streamMergeDecodeBHist (streamMergeEncodeBHist continuation))
            (streamMergeDecodeBHist (streamMergeEncodeBHist provenance))
            (streamMergeDecodeBHist (streamMergeEncodeBHist localName))) =
          some
            (StreamMergeUp.mk sourceLeft sourceRight selector leftWindow rightWindow
              mergedWindow transport continuation provenance localName)
      rw [StreamMergeTasteGate_single_carrier_alignment_decode sourceLeft,
        StreamMergeTasteGate_single_carrier_alignment_decode sourceRight,
        StreamMergeTasteGate_single_carrier_alignment_decode selector,
        StreamMergeTasteGate_single_carrier_alignment_decode leftWindow,
        StreamMergeTasteGate_single_carrier_alignment_decode rightWindow,
        StreamMergeTasteGate_single_carrier_alignment_decode mergedWindow,
        StreamMergeTasteGate_single_carrier_alignment_decode transport,
        StreamMergeTasteGate_single_carrier_alignment_decode continuation,
        StreamMergeTasteGate_single_carrier_alignment_decode provenance,
        StreamMergeTasteGate_single_carrier_alignment_decode localName]

private theorem StreamMergeTasteGate_single_carrier_alignment_injective {x y : StreamMergeUp} :
    streamMergeToEventFlow x = streamMergeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x = streamMergeFromEventFlow (streamMergeToEventFlow x) :=
        (StreamMergeTasteGate_single_carrier_alignment_round_trip x).symm
      _ = streamMergeFromEventFlow (streamMergeToEventFlow y) :=
        congrArg streamMergeFromEventFlow heq
      _ = some y := StreamMergeTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem StreamMergeTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : StreamMergeUp, streamMergeFields x = streamMergeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk sourceLeft₁ sourceRight₁ selector₁ leftWindow₁ rightWindow₁ mergedWindow₁
      transport₁ continuation₁ provenance₁ localName₁ =>
      cases y with
      | mk sourceLeft₂ sourceRight₂ selector₂ leftWindow₂ rightWindow₂ mergedWindow₂
          transport₂ continuation₂ provenance₂ localName₂ =>
          cases h
          rfl

instance streamMergeBHistCarrier : BHistCarrier StreamMergeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamMergeToEventFlow
  fromEventFlow := streamMergeFromEventFlow

instance streamMergeChapterTasteGate : ChapterTasteGate StreamMergeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamMergeFromEventFlow (streamMergeToEventFlow x) = some x
    exact StreamMergeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StreamMergeTasteGate_single_carrier_alignment_injective heq)

instance streamMergeFieldFaithful : FieldFaithful StreamMergeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := streamMergeFields
  field_faithful := StreamMergeTasteGate_single_carrier_alignment_field_faithful

instance streamMergeNontrivial : Nontrivial StreamMergeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StreamMergeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StreamMergeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def streamMergeTasteGate : ChapterTasteGate StreamMergeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  streamMergeChapterTasteGate

theorem StreamMergeTasteGate_single_carrier_alignment :
    (∀ h : BHist, streamMergeDecodeBHist (streamMergeEncodeBHist h) = h) ∧
      (∀ x : StreamMergeUp, streamMergeFromEventFlow (streamMergeToEventFlow x) = some x) ∧
        (∀ x y : StreamMergeUp,
          streamMergeToEventFlow x = streamMergeToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate StreamMergeUp) ∧
            Nonempty (FieldFaithful StreamMergeUp) ∧
              Nonempty (Nontrivial StreamMergeUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact StreamMergeTasteGate_single_carrier_alignment_decode
  · constructor
    · exact StreamMergeTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact StreamMergeTasteGate_single_carrier_alignment_injective heq
      · exact
          ⟨⟨streamMergeChapterTasteGate⟩,
            ⟨streamMergeFieldFaithful⟩,
            ⟨streamMergeNontrivial⟩⟩

end BEDC.Derived.StreamMergeUp.TasteGate
