import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamNameModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamNameModulusUp : Type where
  | mk (S D R E W H C P N : BHist) : StreamNameModulusUp
  deriving DecidableEq

def streamNameModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamNameModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamNameModulusEncodeBHist h

def streamNameModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamNameModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamNameModulusDecodeBHist tail)

private theorem StreamNameModulusTasteGate_single_carrier_alignment_decode :
    forall h : BHist, streamNameModulusDecodeBHist (streamNameModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def streamNameModulusFields : StreamNameModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StreamNameModulusUp.mk S D R E W H C P N => [S, D, R, E, W, H, C, P, N]

def streamNameModulusToEventFlow : StreamNameModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (streamNameModulusFields x).map streamNameModulusEncodeBHist

def streamNameModulusEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => streamNameModulusEventAt index rest

def streamNameModulusFromEventFlow : EventFlow -> Option StreamNameModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (StreamNameModulusUp.mk
          (streamNameModulusDecodeBHist (streamNameModulusEventAt 0 flow))
          (streamNameModulusDecodeBHist (streamNameModulusEventAt 1 flow))
          (streamNameModulusDecodeBHist (streamNameModulusEventAt 2 flow))
          (streamNameModulusDecodeBHist (streamNameModulusEventAt 3 flow))
          (streamNameModulusDecodeBHist (streamNameModulusEventAt 4 flow))
          (streamNameModulusDecodeBHist (streamNameModulusEventAt 5 flow))
          (streamNameModulusDecodeBHist (streamNameModulusEventAt 6 flow))
          (streamNameModulusDecodeBHist (streamNameModulusEventAt 7 flow))
          (streamNameModulusDecodeBHist (streamNameModulusEventAt 8 flow)))

private theorem StreamNameModulusTasteGate_single_carrier_alignment_round_trip :
    forall x : StreamNameModulusUp,
      streamNameModulusFromEventFlow (streamNameModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D R E W H C P N =>
      change
        some
          (StreamNameModulusUp.mk
            (streamNameModulusDecodeBHist (streamNameModulusEncodeBHist S))
            (streamNameModulusDecodeBHist (streamNameModulusEncodeBHist D))
            (streamNameModulusDecodeBHist (streamNameModulusEncodeBHist R))
            (streamNameModulusDecodeBHist (streamNameModulusEncodeBHist E))
            (streamNameModulusDecodeBHist (streamNameModulusEncodeBHist W))
            (streamNameModulusDecodeBHist (streamNameModulusEncodeBHist H))
            (streamNameModulusDecodeBHist (streamNameModulusEncodeBHist C))
            (streamNameModulusDecodeBHist (streamNameModulusEncodeBHist P))
            (streamNameModulusDecodeBHist (streamNameModulusEncodeBHist N))) =
          some (StreamNameModulusUp.mk S D R E W H C P N)
      rw [StreamNameModulusTasteGate_single_carrier_alignment_decode S,
        StreamNameModulusTasteGate_single_carrier_alignment_decode D,
        StreamNameModulusTasteGate_single_carrier_alignment_decode R,
        StreamNameModulusTasteGate_single_carrier_alignment_decode E,
        StreamNameModulusTasteGate_single_carrier_alignment_decode W,
        StreamNameModulusTasteGate_single_carrier_alignment_decode H,
        StreamNameModulusTasteGate_single_carrier_alignment_decode C,
        StreamNameModulusTasteGate_single_carrier_alignment_decode P,
        StreamNameModulusTasteGate_single_carrier_alignment_decode N]

private theorem streamNameModulusToEventFlow_injective {x y : StreamNameModulusUp} :
    streamNameModulusToEventFlow x = streamNameModulusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      streamNameModulusFromEventFlow (streamNameModulusToEventFlow x) =
        streamNameModulusFromEventFlow (streamNameModulusToEventFlow y) :=
    congrArg streamNameModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StreamNameModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StreamNameModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem StreamNameModulusTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : StreamNameModulusUp, streamNameModulusFields x = streamNameModulusFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 D1 R1 E1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 D2 R2 E2 W2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance streamNameModulusBHistCarrier : BHistCarrier StreamNameModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamNameModulusToEventFlow
  fromEventFlow := streamNameModulusFromEventFlow

instance streamNameModulusChapterTasteGate : ChapterTasteGate StreamNameModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamNameModulusFromEventFlow (streamNameModulusToEventFlow x) = some x
    exact StreamNameModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (streamNameModulusToEventFlow_injective heq)

instance streamNameModulusFieldFaithful : FieldFaithful StreamNameModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := streamNameModulusFields
  field_faithful := StreamNameModulusTasteGate_single_carrier_alignment_fields_faithful

instance streamNameModulusNontrivial : Nontrivial StreamNameModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StreamNameModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StreamNameModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StreamNameModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  streamNameModulusChapterTasteGate

theorem StreamNameModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate StreamNameModulusUp) ∧
      Nonempty (FieldFaithful StreamNameModulusUp) ∧
      Nonempty (Nontrivial StreamNameModulusUp) ∧
      (∀ h : BHist, streamNameModulusDecodeBHist (streamNameModulusEncodeBHist h) = h) ∧
      (∀ x : StreamNameModulusUp,
        streamNameModulusFromEventFlow (streamNameModulusToEventFlow x) = some x) ∧
      (∀ x y : StreamNameModulusUp,
        streamNameModulusToEventFlow x = streamNameModulusToEventFlow y -> x = y) ∧
      streamNameModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨streamNameModulusChapterTasteGate⟩,
      ⟨⟨streamNameModulusFieldFaithful⟩,
        ⟨⟨streamNameModulusNontrivial⟩,
          ⟨StreamNameModulusTasteGate_single_carrier_alignment_decode,
            ⟨StreamNameModulusTasteGate_single_carrier_alignment_round_trip,
              ⟨fun _ _ heq => streamNameModulusToEventFlow_injective heq, rfl⟩⟩⟩⟩⟩⟩

end BEDC.Derived.StreamNameModulusUp
