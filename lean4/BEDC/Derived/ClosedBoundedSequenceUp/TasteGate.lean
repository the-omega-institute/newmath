import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBoundedSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBoundedSequenceUp : Type where
  | mk (I W R D E H C P N : BHist) : ClosedBoundedSequenceUp
  deriving DecidableEq

def closedBoundedSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBoundedSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBoundedSequenceEncodeBHist h

def closedBoundedSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBoundedSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBoundedSequenceDecodeBHist tail)

private theorem ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedBoundedSequenceFields : ClosedBoundedSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBoundedSequenceUp.mk I W R D E H C P N => [I, W, R, D, E, H, C, P, N]

def closedBoundedSequenceToEventFlow : ClosedBoundedSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (closedBoundedSequenceFields x).map closedBoundedSequenceEncodeBHist

private def closedBoundedSequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedBoundedSequenceEventAtDefault index rest

def closedBoundedSequenceFromEventFlow (ef : EventFlow) : Option ClosedBoundedSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedBoundedSequenceUp.mk
      (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAtDefault 0 ef))
      (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAtDefault 1 ef))
      (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAtDefault 2 ef))
      (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAtDefault 3 ef))
      (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAtDefault 4 ef))
      (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAtDefault 5 ef))
      (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAtDefault 6 ef))
      (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAtDefault 7 ef))
      (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAtDefault 8 ef)))

private theorem closedBoundedSequence_round_trip :
    ∀ x : ClosedBoundedSequenceUp,
      closedBoundedSequenceFromEventFlow (closedBoundedSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I W R D E H C P N =>
      change
        some
          (ClosedBoundedSequenceUp.mk
            (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist I))
            (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist W))
            (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist R))
            (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist D))
            (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist E))
            (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist H))
            (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist C))
            (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist P))
            (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist N))) =
          some (ClosedBoundedSequenceUp.mk I W R D E H C P N)
      rw [ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode I,
        ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode W,
        ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode R,
        ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode D,
        ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode E,
        ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode H,
        ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode C,
        ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode P,
        ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode N]

private theorem ClosedBoundedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedBoundedSequenceUp} :
    closedBoundedSequenceToEventFlow x = closedBoundedSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedBoundedSequenceFromEventFlow (closedBoundedSequenceToEventFlow x) =
        closedBoundedSequenceFromEventFlow (closedBoundedSequenceToEventFlow y) :=
    congrArg closedBoundedSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedBoundedSequence_round_trip x).symm
      (Eq.trans hread (closedBoundedSequence_round_trip y)))

instance closedBoundedSequenceBHistCarrier : BHistCarrier ClosedBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBoundedSequenceToEventFlow
  fromEventFlow := closedBoundedSequenceFromEventFlow

instance closedBoundedSequenceChapterTasteGate : ChapterTasteGate ClosedBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedBoundedSequenceFromEventFlow (closedBoundedSequenceToEventFlow x) = some x
    exact closedBoundedSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedBoundedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ClosedBoundedSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedBoundedSequenceChapterTasteGate

theorem ClosedBoundedSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist h) = h) ∧
      (∀ x : ClosedBoundedSequenceUp,
        closedBoundedSequenceFromEventFlow (closedBoundedSequenceToEventFlow x) = some x) ∧
        (∀ x y : ClosedBoundedSequenceUp,
          closedBoundedSequenceToEventFlow x = closedBoundedSequenceToEventFlow y → x = y) ∧
          closedBoundedSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ClosedBoundedSequenceTasteGate_single_carrier_alignment_decode,
      closedBoundedSequence_round_trip,
      fun _x _y => ClosedBoundedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.ClosedBoundedSequenceUp
