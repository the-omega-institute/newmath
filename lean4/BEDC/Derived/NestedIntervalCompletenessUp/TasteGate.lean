import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalCompletenessUp : Type where
  | mk (B N C W R E H T P Q : BHist) : NestedIntervalCompletenessUp
  deriving DecidableEq

def NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist h

def NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow :
    NestedIntervalCompletenessUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalCompletenessUp.mk B N C W R E H T P Q =>
      [NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist B,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist N,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist C,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist W,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist R,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist E,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist H,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist T,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist P,
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist Q]

private def NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault index rest

def NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option NestedIntervalCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NestedIntervalCompletenessUp.mk
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip :
    forall x : NestedIntervalCompletenessUp,
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow x) =
          some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B N C W R E H T P Q =>
      change
        some
          (NestedIntervalCompletenessUp.mk
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist B))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist N))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist C))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist W))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist R))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist E))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist H))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist T))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist P))
            (NestedIntervalCompletenessTasteGate_single_carrier_alignment_decodeBHist
              (NestedIntervalCompletenessTasteGate_single_carrier_alignment_encodeBHist Q))) =
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
    NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow x =
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow x) =
        NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow
          (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip y)))

instance nestedIntervalCompletenessBHistCarrier :
    BHistCarrier NestedIntervalCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow

theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment :
    ChapterTasteGate NestedIntervalCompletenessUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change
      NestedIntervalCompletenessTasteGate_single_carrier_alignment_fromEventFlow
        (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
    exact NestedIntervalCompletenessTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy
      (NestedIntervalCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance nestedIntervalCompletenessChapterTasteGate :
    ChapterTasteGate NestedIntervalCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  NestedIntervalCompletenessTasteGate_single_carrier_alignment

end BEDC.Derived.NestedIntervalCompletenessUp
