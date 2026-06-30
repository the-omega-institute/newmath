import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerMonotoneSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerMonotoneSequenceUp : Type where
  | mk
      (S W D R E M H C P N : BHist) :
      BrouwerMonotoneSequenceUp

def brouwerMonotoneSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerMonotoneSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerMonotoneSequenceEncodeBHist h

def brouwerMonotoneSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerMonotoneSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerMonotoneSequenceDecodeBHist tail)

private theorem brouwerMonotoneSequence_decode_encode_bhist :
    ∀ h : BHist,
      brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def brouwerMonotoneSequenceFields : BrouwerMonotoneSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerMonotoneSequenceUp.mk S W D R E M H C P N =>
      [S, W, D, R, E, M, H, C, P, N]

def brouwerMonotoneSequenceToEventFlow : BrouwerMonotoneSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (brouwerMonotoneSequenceFields x).map brouwerMonotoneSequenceEncodeBHist

private def brouwerMonotoneSequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerMonotoneSequenceEventAtDefault index rest

def brouwerMonotoneSequenceFromEventFlow
    (flow : EventFlow) : Option BrouwerMonotoneSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrouwerMonotoneSequenceUp.mk
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 0 flow))
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 1 flow))
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 2 flow))
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 3 flow))
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 4 flow))
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 5 flow))
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 6 flow))
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 7 flow))
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 8 flow))
      (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEventAtDefault 9 flow)))

private theorem brouwerMonotoneSequence_round_trip :
    ∀ x : BrouwerMonotoneSequenceUp,
      brouwerMonotoneSequenceFromEventFlow
        (brouwerMonotoneSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D R E M H C P N =>
      change
        some
          (BrouwerMonotoneSequenceUp.mk
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist S))
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist W))
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist D))
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist R))
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist E))
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist M))
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist H))
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist C))
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist P))
            (brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist N))) =
          some (BrouwerMonotoneSequenceUp.mk S W D R E M H C P N)
      rw [brouwerMonotoneSequence_decode_encode_bhist S,
        brouwerMonotoneSequence_decode_encode_bhist W,
        brouwerMonotoneSequence_decode_encode_bhist D,
        brouwerMonotoneSequence_decode_encode_bhist R,
        brouwerMonotoneSequence_decode_encode_bhist E,
        brouwerMonotoneSequence_decode_encode_bhist M,
        brouwerMonotoneSequence_decode_encode_bhist H,
        brouwerMonotoneSequence_decode_encode_bhist C,
        brouwerMonotoneSequence_decode_encode_bhist P,
        brouwerMonotoneSequence_decode_encode_bhist N]

private theorem brouwerMonotoneSequenceToEventFlow_injective
    {x y : BrouwerMonotoneSequenceUp} :
    brouwerMonotoneSequenceToEventFlow x = brouwerMonotoneSequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerMonotoneSequenceFromEventFlow (brouwerMonotoneSequenceToEventFlow x) =
        brouwerMonotoneSequenceFromEventFlow (brouwerMonotoneSequenceToEventFlow y) :=
    congrArg brouwerMonotoneSequenceFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (brouwerMonotoneSequence_round_trip x).symm
        (Eq.trans hread (brouwerMonotoneSequence_round_trip y)))

instance brouwerMonotoneSequenceBHistCarrier :
    BHistCarrier BrouwerMonotoneSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerMonotoneSequenceToEventFlow
  fromEventFlow := brouwerMonotoneSequenceFromEventFlow

instance brouwerMonotoneSequenceChapterTasteGate :
    ChapterTasteGate BrouwerMonotoneSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      brouwerMonotoneSequenceFromEventFlow
        (brouwerMonotoneSequenceToEventFlow x) = some x
    exact brouwerMonotoneSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (brouwerMonotoneSequenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BrouwerMonotoneSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  brouwerMonotoneSequenceChapterTasteGate

theorem BrouwerMonotoneSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      brouwerMonotoneSequenceDecodeBHist (brouwerMonotoneSequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BrouwerMonotoneSequenceUp) ∧
        Nonempty (ChapterTasteGate BrouwerMonotoneSequenceUp) ∧
          brouwerMonotoneSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨brouwerMonotoneSequence_decode_encode_bhist,
      ⟨brouwerMonotoneSequenceBHistCarrier⟩,
      ⟨brouwerMonotoneSequenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BrouwerMonotoneSequenceUp
