import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalCompletenessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalCompletenessUp : Type where
  | mk (B N C W R E H T P Q : BHist) : NestedIntervalCompletenessUp
  deriving DecidableEq

def nestedIntervalCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalCompletenessEncodeBHist h

def nestedIntervalCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalCompletenessDecodeBHist tail)

private theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedIntervalCompletenessFields : NestedIntervalCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalCompletenessUp.mk B N C W R E H T P Q => [B, N, C, W, R, E, H, T, P, Q]

def nestedIntervalCompletenessToEventFlow : NestedIntervalCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedIntervalCompletenessFields x).map nestedIntervalCompletenessEncodeBHist

private def nestedIntervalCompletenessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedIntervalCompletenessEventAt index rest

def nestedIntervalCompletenessFromEventFlow (ef : EventFlow) :
    Option NestedIntervalCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NestedIntervalCompletenessUp.mk
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 0 ef))
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 1 ef))
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 2 ef))
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 3 ef))
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 4 ef))
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 5 ef))
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 6 ef))
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 7 ef))
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 8 ef))
      (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEventAt 9 ef)))

private theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NestedIntervalCompletenessUp,
      nestedIntervalCompletenessFromEventFlow (nestedIntervalCompletenessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B N C W R E H T P Q =>
      change
        some
          (NestedIntervalCompletenessUp.mk
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist B))
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist N))
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist C))
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist W))
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist R))
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist E))
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist H))
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist T))
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist P))
            (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist Q))) =
          some (NestedIntervalCompletenessUp.mk B N C W R E H T P Q)
      rw [NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode B,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode N,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode C,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode W,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode R,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode E,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode H,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode T,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode P,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode Q]

private theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NestedIntervalCompletenessUp} :
    nestedIntervalCompletenessToEventFlow x = nestedIntervalCompletenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedIntervalCompletenessFromEventFlow (nestedIntervalCompletenessToEventFlow x) =
        nestedIntervalCompletenessFromEventFlow (nestedIntervalCompletenessToEventFlow y) :=
    congrArg nestedIntervalCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip y)))

instance nestedIntervalCompletenessBHistCarrier : BHistCarrier NestedIntervalCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalCompletenessToEventFlow
  fromEventFlow := nestedIntervalCompletenessFromEventFlow

local instance nestedIntervalCompletenessChapterTasteGate :
    ChapterTasteGate NestedIntervalCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedIntervalCompletenessFromEventFlow (nestedIntervalCompletenessToEventFlow x) =
        some x
    exact NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist h) = h) ∧
      (∀ x : NestedIntervalCompletenessUp,
        nestedIntervalCompletenessFromEventFlow (nestedIntervalCompletenessToEventFlow x) =
          some x) ∧
        (∀ x y : NestedIntervalCompletenessUp,
          nestedIntervalCompletenessToEventFlow x =
            nestedIntervalCompletenessToEventFlow y → x = y) ∧
          nestedIntervalCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode,
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip,
      (by
        intro x y heq
        exact NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NestedIntervalCompletenessUp.TasteGate
