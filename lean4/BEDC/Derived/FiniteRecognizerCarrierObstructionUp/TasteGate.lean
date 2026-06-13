import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteRecognizerCarrierObstructionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteRecognizerCarrierObstructionUp : Type where
  | packet
      (accept generated gate tuple readback transport tasteGate hsameRow replay provenance
        localName : BHist) :
      FiniteRecognizerCarrierObstructionUp
  deriving DecidableEq

def finiteRecognizerCarrierObstructionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteRecognizerCarrierObstructionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteRecognizerCarrierObstructionEncodeBHist h

def finiteRecognizerCarrierObstructionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteRecognizerCarrierObstructionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteRecognizerCarrierObstructionDecodeBHist tail)

private theorem finiteRecognizerCarrierObstructionDecodeEncode :
    ∀ h : BHist,
      finiteRecognizerCarrierObstructionDecodeBHist
          (finiteRecognizerCarrierObstructionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteRecognizerCarrierObstructionFields :
    FiniteRecognizerCarrierObstructionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRecognizerCarrierObstructionUp.packet accept generated gate tuple readback transport
      tasteGate hsameRow replay provenance localName =>
      [accept, generated, gate, tuple, readback, transport, tasteGate, hsameRow, replay,
        provenance, localName]

def finiteRecognizerCarrierObstructionToEventFlow :
    FiniteRecognizerCarrierObstructionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (finiteRecognizerCarrierObstructionFields x).map
        finiteRecognizerCarrierObstructionEncodeBHist

private def finiteRecognizerCarrierObstructionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteRecognizerCarrierObstructionEventAt index rest

def finiteRecognizerCarrierObstructionFromEventFlow
    (ef : EventFlow) : Option FiniteRecognizerCarrierObstructionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteRecognizerCarrierObstructionUp.packet
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 0 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 1 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 2 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 3 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 4 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 5 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 6 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 7 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 8 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 9 ef))
      (finiteRecognizerCarrierObstructionDecodeBHist
        (finiteRecognizerCarrierObstructionEventAt 10 ef)))

private theorem finiteRecognizerCarrierObstruction_round_trip
    (x : FiniteRecognizerCarrierObstructionUp) :
    finiteRecognizerCarrierObstructionFromEventFlow
        (finiteRecognizerCarrierObstructionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet accept generated gate tuple readback transport tasteGate hsameRow replay provenance
      localName =>
      change
        some
          (FiniteRecognizerCarrierObstructionUp.packet
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist accept))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist generated))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist gate))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist tuple))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist readback))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist transport))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist tasteGate))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist hsameRow))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist replay))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist provenance))
            (finiteRecognizerCarrierObstructionDecodeBHist
              (finiteRecognizerCarrierObstructionEncodeBHist localName))) =
          some
            (FiniteRecognizerCarrierObstructionUp.packet accept generated gate tuple readback
              transport tasteGate hsameRow replay provenance localName)
      rw [finiteRecognizerCarrierObstructionDecodeEncode accept,
        finiteRecognizerCarrierObstructionDecodeEncode generated,
        finiteRecognizerCarrierObstructionDecodeEncode gate,
        finiteRecognizerCarrierObstructionDecodeEncode tuple,
        finiteRecognizerCarrierObstructionDecodeEncode readback,
        finiteRecognizerCarrierObstructionDecodeEncode transport,
        finiteRecognizerCarrierObstructionDecodeEncode tasteGate,
        finiteRecognizerCarrierObstructionDecodeEncode hsameRow,
        finiteRecognizerCarrierObstructionDecodeEncode replay,
        finiteRecognizerCarrierObstructionDecodeEncode provenance,
        finiteRecognizerCarrierObstructionDecodeEncode localName]

private theorem finiteRecognizerCarrierObstructionToEventFlow_injective
    {x y : FiniteRecognizerCarrierObstructionUp} :
    finiteRecognizerCarrierObstructionToEventFlow x =
        finiteRecognizerCarrierObstructionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteRecognizerCarrierObstructionFromEventFlow
          (finiteRecognizerCarrierObstructionToEventFlow x) =
        finiteRecognizerCarrierObstructionFromEventFlow
          (finiteRecognizerCarrierObstructionToEventFlow y) :=
    congrArg finiteRecognizerCarrierObstructionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteRecognizerCarrierObstruction_round_trip x).symm
      (Eq.trans hread (finiteRecognizerCarrierObstruction_round_trip y)))

private theorem finiteRecognizerCarrierObstructionFieldFaithfulProof :
    ∀ x y : FiniteRecognizerCarrierObstructionUp,
      finiteRecognizerCarrierObstructionFields x =
          finiteRecognizerCarrierObstructionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | packet accept1 generated1 gate1 tuple1 readback1 transport1 tasteGate1 hsameRow1 replay1
      provenance1 localName1 =>
      cases y with
      | packet accept2 generated2 gate2 tuple2 readback2 transport2 tasteGate2 hsameRow2
          replay2 provenance2 localName2 =>
          cases hfields
          rfl

instance finiteRecognizerCarrierObstructionBHistCarrier :
    BHistCarrier FiniteRecognizerCarrierObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteRecognizerCarrierObstructionToEventFlow
  fromEventFlow := finiteRecognizerCarrierObstructionFromEventFlow

instance finiteRecognizerCarrierObstructionChapterTasteGate :
    ChapterTasteGate FiniteRecognizerCarrierObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteRecognizerCarrierObstructionFromEventFlow
          (finiteRecognizerCarrierObstructionToEventFlow x) =
        some x
    exact finiteRecognizerCarrierObstruction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteRecognizerCarrierObstructionToEventFlow_injective heq)

instance finiteRecognizerCarrierObstructionFieldFaithful :
    FieldFaithful FiniteRecognizerCarrierObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteRecognizerCarrierObstructionFields
  field_faithful := finiteRecognizerCarrierObstructionFieldFaithfulProof

instance finiteRecognizerCarrierObstructionNontrivial :
    Nontrivial FiniteRecognizerCarrierObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteRecognizerCarrierObstructionUp.packet BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FiniteRecognizerCarrierObstructionUp.packet (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteRecognizerCarrierObstructionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteRecognizerCarrierObstructionChapterTasteGate

def taste_gate_witness : FieldFaithful FiniteRecognizerCarrierObstructionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteRecognizerCarrierObstructionFieldFaithful

theorem FiniteRecognizerCarrierObstructionUpTasteGate_single_carrier_alignment :
    (∀ x : FiniteRecognizerCarrierObstructionUp,
      finiteRecognizerCarrierObstructionFromEventFlow
          (finiteRecognizerCarrierObstructionToEventFlow x) =
        some x) ∧
      Nonempty (BHistCarrier FiniteRecognizerCarrierObstructionUp) ∧
        Nonempty (ChapterTasteGate FiniteRecognizerCarrierObstructionUp) ∧
          Nonempty (FieldFaithful FiniteRecognizerCarrierObstructionUp) ∧
            finiteRecognizerCarrierObstructionFields
                (FiniteRecognizerCarrierObstructionUp.packet BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty) =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨finiteRecognizerCarrierObstruction_round_trip,
      ⟨finiteRecognizerCarrierObstructionBHistCarrier⟩,
      ⟨finiteRecognizerCarrierObstructionChapterTasteGate⟩,
      ⟨finiteRecognizerCarrierObstructionFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.FiniteRecognizerCarrierObstructionUp
