import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneBoundedSequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneBoundedSequenceUp : Type where
  | mk (S W R O B T H C P N : BHist) : MonotoneBoundedSequenceUp
  deriving DecidableEq

def monotoneBoundedSequenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneBoundedSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneBoundedSequenceEncodeBHist h

def monotoneBoundedSequenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneBoundedSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneBoundedSequenceDecodeBHist tail)

private theorem MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneBoundedSequenceFields : MonotoneBoundedSequenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneBoundedSequenceUp.mk S W R O B T H C P N => [S, W, R, O, B, T, H, C, P, N]

def monotoneBoundedSequenceToEventFlow : MonotoneBoundedSequenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (monotoneBoundedSequenceFields x).map monotoneBoundedSequenceEncodeBHist

private def monotoneBoundedSequenceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneBoundedSequenceEventAtDefault index rest

def monotoneBoundedSequenceFromEventFlow : EventFlow -> Option MonotoneBoundedSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MonotoneBoundedSequenceUp.mk
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 0 ef))
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 1 ef))
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 2 ef))
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 3 ef))
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 4 ef))
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 5 ef))
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 6 ef))
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 7 ef))
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 8 ef))
          (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEventAtDefault 9 ef)))

private theorem MonotoneBoundedSequenceTasteGate_single_carrier_alignment_round_trip :
    forall x : MonotoneBoundedSequenceUp,
      monotoneBoundedSequenceFromEventFlow (monotoneBoundedSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W R O B T H C P N =>
      change
        some
          (MonotoneBoundedSequenceUp.mk
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist S))
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist W))
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist R))
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist O))
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist B))
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist T))
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist H))
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist C))
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist P))
            (monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist N))) =
          some (MonotoneBoundedSequenceUp.mk S W R O B T H C P N)
      rw [MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode S,
        MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode W,
        MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode R,
        MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode O,
        MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode B,
        MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode T,
        MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode H,
        MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode C,
        MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode P,
        MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem MonotoneBoundedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MonotoneBoundedSequenceUp} :
    monotoneBoundedSequenceToEventFlow x = monotoneBoundedSequenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneBoundedSequenceFromEventFlow (monotoneBoundedSequenceToEventFlow x) =
        monotoneBoundedSequenceFromEventFlow (monotoneBoundedSequenceToEventFlow y) :=
    congrArg monotoneBoundedSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MonotoneBoundedSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MonotoneBoundedSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem MonotoneBoundedSequenceTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : MonotoneBoundedSequenceUp,
      monotoneBoundedSequenceFields x = monotoneBoundedSequenceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 W1 R1 O1 B1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 R2 O2 B2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance monotoneBoundedSequenceBHistCarrier :
    BHistCarrier MonotoneBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneBoundedSequenceToEventFlow
  fromEventFlow := monotoneBoundedSequenceFromEventFlow

instance monotoneBoundedSequenceChapterTasteGate :
    ChapterTasteGate MonotoneBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change monotoneBoundedSequenceFromEventFlow (monotoneBoundedSequenceToEventFlow x) =
      some x
    exact MonotoneBoundedSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MonotoneBoundedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance monotoneBoundedSequenceFieldFaithful :
    FieldFaithful MonotoneBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := monotoneBoundedSequenceFields
  field_faithful := MonotoneBoundedSequenceTasteGate_single_carrier_alignment_fields_faithful

instance monotoneBoundedSequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MonotoneBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MonotoneBoundedSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MonotoneBoundedSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MonotoneBoundedSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monotoneBoundedSequenceChapterTasteGate

theorem MonotoneBoundedSequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MonotoneBoundedSequenceUp) ∧
      Nonempty (FieldFaithful MonotoneBoundedSequenceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MonotoneBoundedSequenceUp) ∧
          (∀ h : BHist,
            monotoneBoundedSequenceDecodeBHist (monotoneBoundedSequenceEncodeBHist h) = h) ∧
            (∀ x : MonotoneBoundedSequenceUp,
              monotoneBoundedSequenceFromEventFlow
                  (monotoneBoundedSequenceToEventFlow x) =
                some x) ∧
              (∀ x y : MonotoneBoundedSequenceUp,
                monotoneBoundedSequenceToEventFlow x = monotoneBoundedSequenceToEventFlow y ->
                  x = y) ∧
                monotoneBoundedSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨monotoneBoundedSequenceChapterTasteGate⟩,
      ⟨⟨monotoneBoundedSequenceFieldFaithful⟩,
        ⟨⟨monotoneBoundedSequenceNontrivial⟩,
          ⟨MonotoneBoundedSequenceTasteGate_single_carrier_alignment_decode_encode,
            ⟨MonotoneBoundedSequenceTasteGate_single_carrier_alignment_round_trip,
              ⟨(fun _ _ heq =>
                MonotoneBoundedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
                  heq),
                rfl⟩⟩⟩⟩⟩⟩

end BEDC.Derived.MonotoneBoundedSequenceUp.TasteGate
