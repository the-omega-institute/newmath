import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmptyBoundaryStepUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EmptyBoundaryStepUp : Type where
  | mk (source enactedMark result ext transport continuation provenance localName : BHist) :
      EmptyBoundaryStepUp
  deriving DecidableEq

def emptyBoundaryStepEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: emptyBoundaryStepEncodeBHist h
  | BHist.e1 h => BMark.b1 :: emptyBoundaryStepEncodeBHist h

def emptyBoundaryStepDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (emptyBoundaryStepDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (emptyBoundaryStepDecodeBHist tail)

private theorem EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def emptyBoundaryStepFields : EmptyBoundaryStepUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EmptyBoundaryStepUp.mk source enactedMark result ext transport continuation provenance
      localName =>
      [source, enactedMark, result, ext, transport, continuation, provenance, localName]

def emptyBoundaryStepToEventFlow : EmptyBoundaryStepUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (emptyBoundaryStepFields x).map emptyBoundaryStepEncodeBHist

private def emptyBoundaryStepEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => emptyBoundaryStepEventAtDefault index rest

def emptyBoundaryStepFromEventFlow : EventFlow → Option EmptyBoundaryStepUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (EmptyBoundaryStepUp.mk
        (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEventAtDefault 0 ef))
        (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEventAtDefault 1 ef))
        (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEventAtDefault 2 ef))
        (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEventAtDefault 3 ef))
        (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEventAtDefault 4 ef))
        (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEventAtDefault 5 ef))
        (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEventAtDefault 6 ef))
        (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEventAtDefault 7 ef)))

def emptyBoundaryStepCarrier : BHistCarrier EmptyBoundaryStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := emptyBoundaryStepToEventFlow
  fromEventFlow := emptyBoundaryStepFromEventFlow

instance emptyBoundaryStepBHistCarrier : BHistCarrier EmptyBoundaryStepUp :=
  -- BEDC touchpoint anchor: BHist BMark
  emptyBoundaryStepCarrier

private theorem EmptyBoundaryStepTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EmptyBoundaryStepUp,
      emptyBoundaryStepFromEventFlow (emptyBoundaryStepToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk source enactedMark result ext transport continuation provenance localName =>
      change
        some
            (EmptyBoundaryStepUp.mk
              (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist source))
              (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist enactedMark))
              (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist result))
              (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist ext))
              (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist transport))
              (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist continuation))
              (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist provenance))
              (emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist localName))) =
          some
            (EmptyBoundaryStepUp.mk source enactedMark result ext transport continuation
              provenance localName)
      rw [EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode source]
      rw [EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode enactedMark]
      rw [EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode result]
      rw [EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode ext]
      rw [EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode transport]
      rw [EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode continuation]
      rw [EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode localName]

private theorem EmptyBoundaryStepTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EmptyBoundaryStepUp} :
    emptyBoundaryStepToEventFlow x = emptyBoundaryStepToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = emptyBoundaryStepFromEventFlow (emptyBoundaryStepToEventFlow x) :=
        (EmptyBoundaryStepTasteGate_single_carrier_alignment_round_trip x).symm
      _ = emptyBoundaryStepFromEventFlow (emptyBoundaryStepToEventFlow y) :=
        congrArg emptyBoundaryStepFromEventFlow hxy
      _ = some y := EmptyBoundaryStepTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def emptyBoundaryStepGate : @ChapterTasteGate EmptyBoundaryStepUp emptyBoundaryStepCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change emptyBoundaryStepFromEventFlow (emptyBoundaryStepToEventFlow x) = some x
    exact EmptyBoundaryStepTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EmptyBoundaryStepTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance emptyBoundaryStepChapterTasteGate : ChapterTasteGate EmptyBoundaryStepUp :=
  -- BEDC touchpoint anchor: BHist BMark
  emptyBoundaryStepGate

theorem EmptyBoundaryStepTasteGate_single_carrier_alignment :
    (∀ h : BHist, emptyBoundaryStepDecodeBHist (emptyBoundaryStepEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EmptyBoundaryStepUp) ∧
        Nonempty (ChapterTasteGate EmptyBoundaryStepUp) ∧
          emptyBoundaryStepEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨EmptyBoundaryStepTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨emptyBoundaryStepCarrier⟩, ⟨⟨emptyBoundaryStepGate⟩, rfl⟩⟩⟩

end BEDC.Derived.EmptyBoundaryStepUp
