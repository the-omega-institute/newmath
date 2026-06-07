import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EventuallyConstantSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EventuallyConstantSequenceUp : Type where
  | mk (S T F R L A H C P N : BHist) : EventuallyConstantSequenceUp
  deriving DecidableEq

def eventuallyConstantSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eventuallyConstantSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eventuallyConstantSequenceEncodeBHist h

def eventuallyConstantSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eventuallyConstantSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eventuallyConstantSequenceDecodeBHist tail)

private theorem EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eventuallyConstantSequenceFields : EventuallyConstantSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EventuallyConstantSequenceUp.mk S T F R L A H C P N => [S, T, F, R, L, A, H, C, P, N]

def eventuallyConstantSequenceToEventFlow : EventuallyConstantSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (eventuallyConstantSequenceFields x).map eventuallyConstantSequenceEncodeBHist

private def eventuallyConstantSequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eventuallyConstantSequenceEventAtDefault index rest

def eventuallyConstantSequenceFromEventFlow
    (ef : EventFlow) : Option EventuallyConstantSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EventuallyConstantSequenceUp.mk
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 0 ef))
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 1 ef))
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 2 ef))
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 3 ef))
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 4 ef))
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 5 ef))
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 6 ef))
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 7 ef))
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 8 ef))
      (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEventAtDefault 9 ef)))

private theorem EventuallyConstantSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EventuallyConstantSequenceUp,
      eventuallyConstantSequenceFromEventFlow (eventuallyConstantSequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T F R L A H C P N =>
      change
        some
          (EventuallyConstantSequenceUp.mk
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist S))
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist T))
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist F))
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist R))
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist L))
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist A))
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist H))
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist C))
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist P))
            (eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist N))) =
          some (EventuallyConstantSequenceUp.mk S T F R L A H C P N)
      rw [EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode S,
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode T,
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode F,
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode R,
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode L,
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode A,
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode H,
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode C,
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode P,
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode N]

private theorem EventuallyConstantSequenceTasteGate_single_carrier_alignment_injective
    {x y : EventuallyConstantSequenceUp} :
    eventuallyConstantSequenceToEventFlow x = eventuallyConstantSequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eventuallyConstantSequenceFromEventFlow (eventuallyConstantSequenceToEventFlow x) =
        eventuallyConstantSequenceFromEventFlow (eventuallyConstantSequenceToEventFlow y) :=
    congrArg eventuallyConstantSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EventuallyConstantSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EventuallyConstantSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem EventuallyConstantSequenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : EventuallyConstantSequenceUp,
      eventuallyConstantSequenceFields x = eventuallyConstantSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 F1 R1 L1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 F2 R2 L2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance eventuallyConstantSequenceBHistCarrier : BHistCarrier EventuallyConstantSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eventuallyConstantSequenceToEventFlow
  fromEventFlow := eventuallyConstantSequenceFromEventFlow

instance eventuallyConstantSequenceChapterTasteGate :
    ChapterTasteGate EventuallyConstantSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eventuallyConstantSequenceFromEventFlow (eventuallyConstantSequenceToEventFlow x) =
      some x
    exact EventuallyConstantSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EventuallyConstantSequenceTasteGate_single_carrier_alignment_injective heq)

instance eventuallyConstantSequenceFieldFaithful : FieldFaithful EventuallyConstantSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eventuallyConstantSequenceFields
  field_faithful := EventuallyConstantSequenceTasteGate_single_carrier_alignment_fields

instance eventuallyConstantSequenceNontrivial : Nontrivial EventuallyConstantSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EventuallyConstantSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EventuallyConstantSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EventuallyConstantSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eventuallyConstantSequenceChapterTasteGate

theorem EventuallyConstantSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      eventuallyConstantSequenceDecodeBHist (eventuallyConstantSequenceEncodeBHist h) = h) ∧
      (∀ x : EventuallyConstantSequenceUp,
        eventuallyConstantSequenceFromEventFlow (eventuallyConstantSequenceToEventFlow x) =
          some x) ∧
        (∀ x y : EventuallyConstantSequenceUp,
          eventuallyConstantSequenceToEventFlow x = eventuallyConstantSequenceToEventFlow y →
            x = y) ∧
          eventuallyConstantSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨EventuallyConstantSequenceTasteGate_single_carrier_alignment_decode,
      EventuallyConstantSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        EventuallyConstantSequenceTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.EventuallyConstantSequenceUp
