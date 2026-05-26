import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialCompactUp : Type where
  | mk (K B S W R E H C P N : BHist) : SequentialCompactUp
  deriving DecidableEq

def sequentialCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialCompactEncodeBHist h

def sequentialCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialCompactDecodeBHist tail)

private theorem SequentialCompactTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, sequentialCompactDecodeBHist (sequentialCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentialCompactFields : SequentialCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialCompactUp.mk K B S W R E H C P N => [K, B, S, W, R, E, H, C, P, N]

def sequentialCompactToEventFlow : SequentialCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentialCompactFields x).map sequentialCompactEncodeBHist

private def sequentialCompactRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentialCompactRawAt index rest

private def sequentialCompactLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => sequentialCompactLengthEq index rest

def sequentialCompactFromEventFlow : EventFlow → Option SequentialCompactUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match sequentialCompactLengthEq 10 flow with
      | true =>
          some
            (SequentialCompactUp.mk
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 0 flow))
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 1 flow))
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 2 flow))
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 3 flow))
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 4 flow))
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 5 flow))
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 6 flow))
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 7 flow))
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 8 flow))
              (sequentialCompactDecodeBHist (sequentialCompactRawAt 9 flow)))
      | false => none

private theorem sequentialCompact_round_trip :
    ∀ x : SequentialCompactUp,
      sequentialCompactFromEventFlow (sequentialCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K B S W R E H C P N =>
      change
        some
          (SequentialCompactUp.mk
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist K))
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist B))
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist S))
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist W))
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist R))
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist E))
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist H))
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist C))
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist P))
            (sequentialCompactDecodeBHist (sequentialCompactEncodeBHist N))) =
          some (SequentialCompactUp.mk K B S W R E H C P N)
      rw [SequentialCompactTasteGate_single_carrier_alignment_decode_encode K,
        SequentialCompactTasteGate_single_carrier_alignment_decode_encode B,
        SequentialCompactTasteGate_single_carrier_alignment_decode_encode S,
        SequentialCompactTasteGate_single_carrier_alignment_decode_encode W,
        SequentialCompactTasteGate_single_carrier_alignment_decode_encode R,
        SequentialCompactTasteGate_single_carrier_alignment_decode_encode E,
        SequentialCompactTasteGate_single_carrier_alignment_decode_encode H,
        SequentialCompactTasteGate_single_carrier_alignment_decode_encode C,
        SequentialCompactTasteGate_single_carrier_alignment_decode_encode P,
        SequentialCompactTasteGate_single_carrier_alignment_decode_encode N]

private theorem sequentialCompactToEventFlow_injective {x y : SequentialCompactUp} :
    sequentialCompactToEventFlow x = sequentialCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialCompactFromEventFlow (sequentialCompactToEventFlow x) =
        sequentialCompactFromEventFlow (sequentialCompactToEventFlow y) :=
    congrArg sequentialCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sequentialCompact_round_trip x).symm
      (Eq.trans hread (sequentialCompact_round_trip y)))

instance sequentialCompactBHistCarrier : BHistCarrier SequentialCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialCompactToEventFlow
  fromEventFlow := sequentialCompactFromEventFlow

instance sequentialCompactChapterTasteGate : ChapterTasteGate SequentialCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentialCompactFromEventFlow (sequentialCompactToEventFlow x) = some x
    exact sequentialCompact_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sequentialCompactToEventFlow_injective heq)

namespace TasteGate

theorem SequentialCompactTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SequentialCompactUp) ∧
      Nonempty (ChapterTasteGate SequentialCompactUp) ∧
        (∀ x : SequentialCompactUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨Nonempty.intro sequentialCompactBHistCarrier,
      Nonempty.intro sequentialCompactChapterTasteGate,
      ChapterTasteGate.round_trip⟩

end TasteGate

end BEDC.Derived.SequentialCompactUp
