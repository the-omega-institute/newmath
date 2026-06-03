import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChoiceWindowSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChoiceWindowSequenceUp : Type where
  | mk : (Q L B S I A O H C P N : BHist) -> ChoiceWindowSequenceUp

def choiceWindowSequenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: choiceWindowSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: choiceWindowSequenceEncodeBHist h

def choiceWindowSequenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (choiceWindowSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (choiceWindowSequenceDecodeBHist tail)

theorem ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def choiceWindowSequenceFields : ChoiceWindowSequenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChoiceWindowSequenceUp.mk Q L B S I A O H C P N => [Q, L, B, S, I, A, O, H, C, P, N]

def choiceWindowSequenceToEventFlow : ChoiceWindowSequenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (choiceWindowSequenceFields x).map choiceWindowSequenceEncodeBHist

def choiceWindowSequenceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => choiceWindowSequenceEventAtDefault index rest

def choiceWindowSequenceFromEventFlow : EventFlow -> Option ChoiceWindowSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ChoiceWindowSequenceUp.mk
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 0 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 1 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 2 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 3 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 4 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 5 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 6 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 7 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 8 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 9 ef))
          (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEventAtDefault 10 ef)))

theorem ChoiceWindowSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ChoiceWindowSequenceUp,
      choiceWindowSequenceFromEventFlow (choiceWindowSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q L B S I A O H C P N =>
      change
        some
          (ChoiceWindowSequenceUp.mk
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist Q))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist L))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist B))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist S))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist I))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist A))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist O))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist H))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist C))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist P))
            (choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist N))) =
          some (ChoiceWindowSequenceUp.mk Q L B S I A O H C P N)
      rw [ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode Q,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode L,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode B,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode S,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode I,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode A,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode O,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode H,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode C,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode P,
        ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode N]

theorem ChoiceWindowSequenceTasteGate_single_carrier_alignment_injective
    {x y : ChoiceWindowSequenceUp} :
    choiceWindowSequenceToEventFlow x = choiceWindowSequenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      choiceWindowSequenceFromEventFlow (choiceWindowSequenceToEventFlow x) =
        choiceWindowSequenceFromEventFlow (choiceWindowSequenceToEventFlow y) :=
    congrArg choiceWindowSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ChoiceWindowSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ChoiceWindowSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance choiceWindowSequenceBHistCarrier : BHistCarrier ChoiceWindowSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := choiceWindowSequenceToEventFlow
  fromEventFlow := choiceWindowSequenceFromEventFlow

instance choiceWindowSequenceChapterTasteGate : ChapterTasteGate ChoiceWindowSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => ChoiceWindowSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ChoiceWindowSequenceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate ChoiceWindowSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  choiceWindowSequenceChapterTasteGate

theorem ChoiceWindowSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, choiceWindowSequenceDecodeBHist (choiceWindowSequenceEncodeBHist h) = h) ∧
      (∀ x : ChoiceWindowSequenceUp,
        choiceWindowSequenceFromEventFlow (choiceWindowSequenceToEventFlow x) = some x) ∧
        (∀ x y : ChoiceWindowSequenceUp,
          choiceWindowSequenceToEventFlow x = choiceWindowSequenceToEventFlow y -> x = y) ∧
          choiceWindowSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ChoiceWindowSequenceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ChoiceWindowSequenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ChoiceWindowSequenceTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ChoiceWindowSequenceUp
