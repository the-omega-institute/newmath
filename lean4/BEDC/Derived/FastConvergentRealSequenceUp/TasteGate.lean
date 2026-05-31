import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastConvergentRealSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastConvergentRealSequenceUp : Type where
  | mk (S R D M E H C P N : BHist) : FastConvergentRealSequenceUp
  deriving DecidableEq

def fastConvergentRealSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastConvergentRealSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastConvergentRealSequenceEncodeBHist h

def fastConvergentRealSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastConvergentRealSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastConvergentRealSequenceDecodeBHist tail)

private theorem fastConvergentRealSequence_decode_encode :
    ∀ h : BHist, fastConvergentRealSequenceDecodeBHist
      (fastConvergentRealSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fastConvergentRealSequenceFields : FastConvergentRealSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastConvergentRealSequenceUp.mk S R D M E H C P N => [S, R, D, M, E, H, C, P, N]

def fastConvergentRealSequenceToEventFlow :
    FastConvergentRealSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fastConvergentRealSequenceFields x).map fastConvergentRealSequenceEncodeBHist

private def fastConvergentRealSequenceDecodePacket
    (S R D M E H C P N : RawEvent) : FastConvergentRealSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FastConvergentRealSequenceUp.mk
    (fastConvergentRealSequenceDecodeBHist S)
    (fastConvergentRealSequenceDecodeBHist R)
    (fastConvergentRealSequenceDecodeBHist D)
    (fastConvergentRealSequenceDecodeBHist M)
    (fastConvergentRealSequenceDecodeBHist E)
    (fastConvergentRealSequenceDecodeBHist H)
    (fastConvergentRealSequenceDecodeBHist C)
    (fastConvergentRealSequenceDecodeBHist P)
    (fastConvergentRealSequenceDecodeBHist N)

private def fastConvergentRealSequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => fastConvergentRealSequenceRawAt n rest

private def fastConvergentRealSequenceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => fastConvergentRealSequenceLengthEq n rest

def fastConvergentRealSequenceFromEventFlow
    (flow : EventFlow) : Option FastConvergentRealSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match fastConvergentRealSequenceLengthEq 9 flow with
  | true =>
      some
        (fastConvergentRealSequenceDecodePacket
          (fastConvergentRealSequenceRawAt 0 flow)
          (fastConvergentRealSequenceRawAt 1 flow)
          (fastConvergentRealSequenceRawAt 2 flow)
          (fastConvergentRealSequenceRawAt 3 flow)
          (fastConvergentRealSequenceRawAt 4 flow)
          (fastConvergentRealSequenceRawAt 5 flow)
          (fastConvergentRealSequenceRawAt 6 flow)
          (fastConvergentRealSequenceRawAt 7 flow)
          (fastConvergentRealSequenceRawAt 8 flow))
  | false => none

private theorem fastConvergentRealSequence_round_trip :
    ∀ x : FastConvergentRealSequenceUp,
      fastConvergentRealSequenceFromEventFlow
        (fastConvergentRealSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D M E H C P N =>
      change
        some
          (fastConvergentRealSequenceDecodePacket
            (fastConvergentRealSequenceEncodeBHist S)
            (fastConvergentRealSequenceEncodeBHist R)
            (fastConvergentRealSequenceEncodeBHist D)
            (fastConvergentRealSequenceEncodeBHist M)
            (fastConvergentRealSequenceEncodeBHist E)
            (fastConvergentRealSequenceEncodeBHist H)
            (fastConvergentRealSequenceEncodeBHist C)
            (fastConvergentRealSequenceEncodeBHist P)
            (fastConvergentRealSequenceEncodeBHist N)) =
          some (FastConvergentRealSequenceUp.mk S R D M E H C P N)
      unfold fastConvergentRealSequenceDecodePacket
      rw [fastConvergentRealSequence_decode_encode S,
        fastConvergentRealSequence_decode_encode R,
        fastConvergentRealSequence_decode_encode D,
        fastConvergentRealSequence_decode_encode M,
        fastConvergentRealSequence_decode_encode E,
        fastConvergentRealSequence_decode_encode H,
        fastConvergentRealSequence_decode_encode C,
        fastConvergentRealSequence_decode_encode P,
        fastConvergentRealSequence_decode_encode N]

private theorem fastConvergentRealSequenceToEventFlow_injective
    {x y : FastConvergentRealSequenceUp} :
    fastConvergentRealSequenceToEventFlow x = fastConvergentRealSequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastConvergentRealSequenceFromEventFlow (fastConvergentRealSequenceToEventFlow x) =
        fastConvergentRealSequenceFromEventFlow (fastConvergentRealSequenceToEventFlow y) :=
    congrArg fastConvergentRealSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fastConvergentRealSequence_round_trip x).symm
      (Eq.trans hread (fastConvergentRealSequence_round_trip y)))

instance fastConvergentRealSequenceBHistCarrier :
    BHistCarrier FastConvergentRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastConvergentRealSequenceToEventFlow
  fromEventFlow := fastConvergentRealSequenceFromEventFlow

instance fastConvergentRealSequenceChapterTasteGate :
    ChapterTasteGate FastConvergentRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      fastConvergentRealSequenceFromEventFlow
        (fastConvergentRealSequenceToEventFlow x) = some x
    exact fastConvergentRealSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fastConvergentRealSequenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FastConvergentRealSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fastConvergentRealSequenceChapterTasteGate

theorem FastConvergentRealSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        fastConvergentRealSequenceDecodeBHist
          (fastConvergentRealSequenceEncodeBHist h) = h) ∧
      (∀ x : FastConvergentRealSequenceUp,
        fastConvergentRealSequenceFromEventFlow
          (fastConvergentRealSequenceToEventFlow x) = some x) ∧
        (∀ x y : FastConvergentRealSequenceUp,
          fastConvergentRealSequenceToEventFlow x =
            fastConvergentRealSequenceToEventFlow y ->
              x = y) ∧
          fastConvergentRealSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact fastConvergentRealSequence_decode_encode
  constructor
  · exact fastConvergentRealSequence_round_trip
  constructor
  · intro x y sameFlow
    exact fastConvergentRealSequenceToEventFlow_injective sameFlow
  · rfl

end BEDC.Derived.FastConvergentRealSequenceUp
