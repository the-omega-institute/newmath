import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBoundedSequenceUp.TasteGate

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

private theorem closedBoundedSequenceDecode_encode_bhist :
    ∀ h : BHist,
      closedBoundedSequenceDecodeBHist (closedBoundedSequenceEncodeBHist h) = h := by
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

def closedBoundedSequenceToEventFlow : ClosedBoundedSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedBoundedSequenceFields x).map closedBoundedSequenceEncodeBHist

private def closedBoundedSequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedBoundedSequenceEventAt index rest

def closedBoundedSequenceFromEventFlow : EventFlow → Option ClosedBoundedSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ClosedBoundedSequenceUp.mk
        (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAt 0 ef))
        (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAt 1 ef))
        (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAt 2 ef))
        (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAt 3 ef))
        (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAt 4 ef))
        (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAt 5 ef))
        (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAt 6 ef))
        (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAt 7 ef))
        (closedBoundedSequenceDecodeBHist (closedBoundedSequenceEventAt 8 ef)))

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
      rw [closedBoundedSequenceDecode_encode_bhist I,
        closedBoundedSequenceDecode_encode_bhist W,
        closedBoundedSequenceDecode_encode_bhist R,
        closedBoundedSequenceDecode_encode_bhist D,
        closedBoundedSequenceDecode_encode_bhist E,
        closedBoundedSequenceDecode_encode_bhist H,
        closedBoundedSequenceDecode_encode_bhist C,
        closedBoundedSequenceDecode_encode_bhist P,
        closedBoundedSequenceDecode_encode_bhist N]

private theorem closedBoundedSequenceToEventFlow_injective
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

instance closedBoundedSequenceBHistCarrier :
    BHistCarrier ClosedBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBoundedSequenceToEventFlow
  fromEventFlow := closedBoundedSequenceFromEventFlow

instance closedBoundedSequenceChapterTasteGate :
    ChapterTasteGate ClosedBoundedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedBoundedSequenceFromEventFlow (closedBoundedSequenceToEventFlow x) = some x
    exact closedBoundedSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedBoundedSequenceToEventFlow_injective heq)

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
  exact ⟨closedBoundedSequenceDecode_encode_bhist,
    closedBoundedSequence_round_trip,
    fun _ _ heq => closedBoundedSequenceToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.ClosedBoundedSequenceUp.TasteGate
