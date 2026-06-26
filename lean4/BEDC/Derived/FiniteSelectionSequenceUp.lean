import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSelectionSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSelectionSequenceUp : Type where
  | mk (W D R T C P N : BHist) : FiniteSelectionSequenceUp
  deriving DecidableEq

def finiteSelectionSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSelectionSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSelectionSequenceEncodeBHist h

def finiteSelectionSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSelectionSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSelectionSequenceDecodeBHist tail)

private theorem FiniteSelectionSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteSelectionSequenceFields : FiniteSelectionSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSelectionSequenceUp.mk W D R T C P N => [W, D, R, T, C, P, N]

def finiteSelectionSequenceToEventFlow : FiniteSelectionSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteSelectionSequenceFields x).map finiteSelectionSequenceEncodeBHist

private def finiteSelectionSequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteSelectionSequenceEventAtDefault index rest

def finiteSelectionSequenceFromEventFlow
    (ef : EventFlow) : Option FiniteSelectionSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteSelectionSequenceUp.mk
      (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEventAtDefault 0 ef))
      (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEventAtDefault 1 ef))
      (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEventAtDefault 2 ef))
      (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEventAtDefault 3 ef))
      (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEventAtDefault 4 ef))
      (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEventAtDefault 5 ef))
      (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEventAtDefault 6 ef)))

private theorem FiniteSelectionSequenceTasteGate_single_carrier_alignment_round_trip
    (x : FiniteSelectionSequenceUp) :
    finiteSelectionSequenceFromEventFlow (finiteSelectionSequenceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W D R T C P N =>
      change
        some
          (FiniteSelectionSequenceUp.mk
            (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEncodeBHist W))
            (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEncodeBHist D))
            (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEncodeBHist R))
            (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEncodeBHist T))
            (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEncodeBHist C))
            (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEncodeBHist P))
            (finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEncodeBHist N))) =
          some (FiniteSelectionSequenceUp.mk W D R T C P N)
      rw [FiniteSelectionSequenceTasteGate_single_carrier_alignment_decode_encode W,
        FiniteSelectionSequenceTasteGate_single_carrier_alignment_decode_encode D,
        FiniteSelectionSequenceTasteGate_single_carrier_alignment_decode_encode R,
        FiniteSelectionSequenceTasteGate_single_carrier_alignment_decode_encode T,
        FiniteSelectionSequenceTasteGate_single_carrier_alignment_decode_encode C,
        FiniteSelectionSequenceTasteGate_single_carrier_alignment_decode_encode P,
        FiniteSelectionSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteSelectionSequenceToEventFlow_injective
    {x y : FiniteSelectionSequenceUp} :
    finiteSelectionSequenceToEventFlow x = finiteSelectionSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSelectionSequenceFromEventFlow (finiteSelectionSequenceToEventFlow x) =
        finiteSelectionSequenceFromEventFlow (finiteSelectionSequenceToEventFlow y) :=
    congrArg finiteSelectionSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteSelectionSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteSelectionSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance finiteSelectionSequenceBHistCarrier : BHistCarrier FiniteSelectionSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSelectionSequenceToEventFlow
  fromEventFlow := finiteSelectionSequenceFromEventFlow

instance finiteSelectionSequenceChapterTasteGate :
    ChapterTasteGate FiniteSelectionSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSelectionSequenceFromEventFlow (finiteSelectionSequenceToEventFlow x) = some x
    exact FiniteSelectionSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteSelectionSequenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteSelectionSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteSelectionSequenceChapterTasteGate

theorem FiniteSelectionSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteSelectionSequenceDecodeBHist (finiteSelectionSequenceEncodeBHist h) = h) ∧
      (∀ x : FiniteSelectionSequenceUp,
        finiteSelectionSequenceFromEventFlow (finiteSelectionSequenceToEventFlow x) = some x) ∧
        (∀ x y : FiniteSelectionSequenceUp,
          finiteSelectionSequenceToEventFlow x = finiteSelectionSequenceToEventFlow y → x = y) ∧
          finiteSelectionSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteSelectionSequenceTasteGate_single_carrier_alignment_decode_encode,
      FiniteSelectionSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FiniteSelectionSequenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteSelectionSequenceUp
