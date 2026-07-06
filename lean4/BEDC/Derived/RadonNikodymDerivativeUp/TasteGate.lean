import BEDC.Derived.RadonNikodymDerivativeUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RadonNikodymDerivativeUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RadonNikodymDerivativeUp : Type where
  | mk
      (baseMeasure acMeasure density window integralReadback nullBoundary transport replay
        provenance localName : BHist) : RadonNikodymDerivativeUp
  deriving DecidableEq

def radonNikodymDerivativeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: radonNikodymDerivativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: radonNikodymDerivativeEncodeBHist h

def radonNikodymDerivativeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (radonNikodymDerivativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (radonNikodymDerivativeDecodeBHist tail)

private theorem RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      radonNikodymDerivativeDecodeBHist (radonNikodymDerivativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def radonNikodymDerivativeFields : RadonNikodymDerivativeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RadonNikodymDerivativeUp.mk baseMeasure acMeasure density window integralReadback
      nullBoundary transport replay provenance localName =>
      [baseMeasure, acMeasure, density, window, integralReadback, nullBoundary, transport, replay,
        provenance, localName]

def radonNikodymDerivativeToEventFlow : RadonNikodymDerivativeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (radonNikodymDerivativeFields x).map radonNikodymDerivativeEncodeBHist

private def RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault index rest

def radonNikodymDerivativeFromEventFlow
    (ef : EventFlow) : Option RadonNikodymDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RadonNikodymDerivativeUp.mk
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (radonNikodymDerivativeDecodeBHist
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem RadonNikodymDerivativeTasteGate_single_carrier_alignment_round_trip
    (x : RadonNikodymDerivativeUp) :
    radonNikodymDerivativeFromEventFlow
      (radonNikodymDerivativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk baseMeasure acMeasure density window integralReadback nullBoundary transport replay
      provenance localName =>
      change
        some
          (RadonNikodymDerivativeUp.mk
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist baseMeasure))
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist acMeasure))
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist density))
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist window))
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist integralReadback))
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist nullBoundary))
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist transport))
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist replay))
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist provenance))
            (radonNikodymDerivativeDecodeBHist
              (radonNikodymDerivativeEncodeBHist localName))) =
          some
            (RadonNikodymDerivativeUp.mk baseMeasure acMeasure density window integralReadback
              nullBoundary transport replay provenance localName)
      rw [RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode baseMeasure,
        RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode acMeasure,
        RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode density,
        RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode window,
        RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode integralReadback,
        RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode nullBoundary,
        RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode transport,
        RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode replay,
        RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode provenance,
        RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode localName]

private theorem RadonNikodymDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RadonNikodymDerivativeUp} :
    radonNikodymDerivativeToEventFlow x = radonNikodymDerivativeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      radonNikodymDerivativeFromEventFlow (radonNikodymDerivativeToEventFlow x) =
        radonNikodymDerivativeFromEventFlow (radonNikodymDerivativeToEventFlow y) :=
    congrArg radonNikodymDerivativeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RadonNikodymDerivativeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RadonNikodymDerivativeTasteGate_single_carrier_alignment_round_trip y)))

private theorem radonNikodymDerivativeFieldFaithful :
    ∀ x y : RadonNikodymDerivativeUp,
      radonNikodymDerivativeFields x = radonNikodymDerivativeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk baseMeasure acMeasure density window integralReadback nullBoundary transport replay
      provenance localName =>
      cases y with
      | mk baseMeasure' acMeasure' density' window' integralReadback' nullBoundary' transport'
          replay' provenance' localName' =>
          cases hfields
          rfl

instance radonNikodymDerivativeBHistCarrier :
    BHistCarrier RadonNikodymDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := radonNikodymDerivativeToEventFlow
  fromEventFlow := radonNikodymDerivativeFromEventFlow

instance radonNikodymDerivativeChapterTasteGate :
    ChapterTasteGate RadonNikodymDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change radonNikodymDerivativeFromEventFlow (radonNikodymDerivativeToEventFlow x) = some x
    exact RadonNikodymDerivativeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RadonNikodymDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance radonNikodymDerivativeFieldFaithfulInstance :
    FieldFaithful RadonNikodymDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := radonNikodymDerivativeFields
  field_faithful := radonNikodymDerivativeFieldFaithful

instance radonNikodymDerivativeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RadonNikodymDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RadonNikodymDerivativeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RadonNikodymDerivativeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RadonNikodymDerivativeTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RadonNikodymDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  radonNikodymDerivativeChapterTasteGate

def taste_gate : ChapterTasteGate RadonNikodymDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RadonNikodymDerivativeTasteGate_single_carrier_alignment_taste_gate

theorem RadonNikodymDerivativeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RadonNikodymDerivativeUp) ∧
      Nonempty (FieldFaithful RadonNikodymDerivativeUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RadonNikodymDerivativeUp) ∧
          (∀ h : BHist,
            radonNikodymDerivativeDecodeBHist (radonNikodymDerivativeEncodeBHist h) = h) ∧
            (∀ x : RadonNikodymDerivativeUp,
              radonNikodymDerivativeFromEventFlow
                (radonNikodymDerivativeToEventFlow x) = some x) ∧
              radonNikodymDerivativeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨radonNikodymDerivativeChapterTasteGate⟩
  constructor
  · exact ⟨radonNikodymDerivativeFieldFaithfulInstance⟩
  constructor
  · exact ⟨radonNikodymDerivativeNontrivial⟩
  constructor
  · exact RadonNikodymDerivativeTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact RadonNikodymDerivativeTasteGate_single_carrier_alignment_round_trip
  · rfl

end TasteGate

theorem RadonNikodymDerivativeTasteGate_single_carrier_alignment :
    Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.RadonNikodymDerivativeUp) ∧
      Nonempty (BEDC.Meta.TasteGate.FieldFaithful TasteGate.RadonNikodymDerivativeUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial TasteGate.RadonNikodymDerivativeUp) ∧
          (∀ h : BEDC.FKernel.Hist.BHist,
            TasteGate.radonNikodymDerivativeDecodeBHist
              (TasteGate.radonNikodymDerivativeEncodeBHist h) = h) ∧
            (∀ x : TasteGate.RadonNikodymDerivativeUp,
              TasteGate.radonNikodymDerivativeFromEventFlow
                (TasteGate.radonNikodymDerivativeToEventFlow x) = some x) ∧
              TasteGate.radonNikodymDerivativeEncodeBHist BEDC.FKernel.Hist.BHist.Empty =
                ([] : BEDC.GroundCompiler.EventFlow.RawEvent) := by
  exact TasteGate.RadonNikodymDerivativeTasteGate_single_carrier_alignment

end BEDC.Derived.RadonNikodymDerivativeUp
