import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NewtonPolygonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NewtonPolygonUp : Type where
  | mk (A V T Q F S H C P N : BHist) : NewtonPolygonUp
  deriving DecidableEq

def NewtonPolygonTasteGate_single_carrier_alignment_fields :
    NewtonPolygonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NewtonPolygonUp.mk A V T Q F S H C P N => [A, V, T, Q, F, S, H, C, P, N]

def NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist h

def NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem NewtonPolygonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow :
    NewtonPolygonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NewtonPolygonUp.mk A V T Q F S H C P N =>
      [NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist A,
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist V,
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist T,
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist Q,
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist F,
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist S,
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist H,
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist C,
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist P,
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist N]

private def NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault index rest

def NewtonPolygonTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option NewtonPolygonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NewtonPolygonUp.mk
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
        (NewtonPolygonTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem NewtonPolygonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NewtonPolygonUp,
      NewtonPolygonTasteGate_single_carrier_alignment_fromEventFlow
        (NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A V T Q F S H C P N =>
      change
        some
          (NewtonPolygonUp.mk
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist A))
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist V))
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist T))
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist Q))
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist F))
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist S))
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist H))
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist C))
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist P))
            (NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
              (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (NewtonPolygonUp.mk A V T Q F S H C P N)
      rw [NewtonPolygonTasteGate_single_carrier_alignment_decode_encode A,
        NewtonPolygonTasteGate_single_carrier_alignment_decode_encode V,
        NewtonPolygonTasteGate_single_carrier_alignment_decode_encode T,
        NewtonPolygonTasteGate_single_carrier_alignment_decode_encode Q,
        NewtonPolygonTasteGate_single_carrier_alignment_decode_encode F,
        NewtonPolygonTasteGate_single_carrier_alignment_decode_encode S,
        NewtonPolygonTasteGate_single_carrier_alignment_decode_encode H,
        NewtonPolygonTasteGate_single_carrier_alignment_decode_encode C,
        NewtonPolygonTasteGate_single_carrier_alignment_decode_encode P,
        NewtonPolygonTasteGate_single_carrier_alignment_decode_encode N]

private theorem NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NewtonPolygonUp} :
    NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow x =
      NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      NewtonPolygonTasteGate_single_carrier_alignment_fromEventFlow
          (NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow x) =
        NewtonPolygonTasteGate_single_carrier_alignment_fromEventFlow
          (NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg NewtonPolygonTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NewtonPolygonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NewtonPolygonTasteGate_single_carrier_alignment_round_trip y)))

instance NewtonPolygonTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier NewtonPolygonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := NewtonPolygonTasteGate_single_carrier_alignment_fromEventFlow

instance NewtonPolygonTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate NewtonPolygonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      NewtonPolygonTasteGate_single_carrier_alignment_fromEventFlow
        (NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact NewtonPolygonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NewtonPolygonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem NewtonPolygonTasteGate_single_carrier_alignment :
    (∀ A V T Q F S H C P N : BHist,
      NewtonPolygonTasteGate_single_carrier_alignment_fields
        (NewtonPolygonUp.mk A V T Q F S H C P N) = [A, V, T, Q, F, S, H, C, P, N]) ∧
      (∀ h : BHist,
        NewtonPolygonTasteGate_single_carrier_alignment_decodeBHist
          (NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        NewtonPolygonTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro A V T Q F S H C P N
    rfl
  · constructor
    · exact NewtonPolygonTasteGate_single_carrier_alignment_decode_encode
    · rfl

end BEDC.Derived.NewtonPolygonUp
