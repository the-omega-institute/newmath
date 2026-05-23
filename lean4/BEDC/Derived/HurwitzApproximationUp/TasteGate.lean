import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HurwitzApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HurwitzApproximationUp : Type where
  | mk (X Q A C F S D R E T U P N : BHist) : HurwitzApproximationUp
  deriving DecidableEq

def HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist h

def HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
        (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def HurwitzApproximationTasteGate_single_carrier_alignment_fields :
    HurwitzApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HurwitzApproximationUp.mk X Q A C F S D R E T U P N =>
      [X, Q, A, C, F, S, D, R, E, T, U, P, N]

def HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow :
    HurwitzApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b1, BMark.b0, BMark.b1, BMark.b0] ::
        (HurwitzApproximationTasteGate_single_carrier_alignment_fields x).map
          HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist

private def HurwitzApproximationTasteGate_single_carrier_alignment_event_at :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      HurwitzApproximationTasteGate_single_carrier_alignment_event_at index rest

def HurwitzApproximationTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option HurwitzApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [BMark.b1, BMark.b0, BMark.b1, BMark.b0] :: rows =>
      some
        (HurwitzApproximationUp.mk
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 0 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 1 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 2 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 3 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 4 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 5 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 6 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 7 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 8 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 9 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 10 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 11 rows))
          (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
            (HurwitzApproximationTasteGate_single_carrier_alignment_event_at 12 rows)))
  | _ => none

private theorem HurwitzApproximationTasteGate_single_carrier_alignment_round_trip
    (x : HurwitzApproximationUp) :
    HurwitzApproximationTasteGate_single_carrier_alignment_fromEventFlow
      (HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Q A C F S D R E T U P N =>
      change
        some
          (HurwitzApproximationUp.mk
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist X))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist Q))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist A))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist C))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist F))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist S))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist D))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist R))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist E))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist T))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist U))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist P))
            (HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
              (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (HurwitzApproximationUp.mk X Q A C F S D R E T U P N)
      rw [HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode X,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode Q,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode A,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode C,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode F,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode S,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode D,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode R,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode E,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode T,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode U,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode P,
        HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode N]

private theorem HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HurwitzApproximationUp} :
    HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow x =
      HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      HurwitzApproximationTasteGate_single_carrier_alignment_fromEventFlow
          (HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow x) =
        HurwitzApproximationTasteGate_single_carrier_alignment_fromEventFlow
          (HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg HurwitzApproximationTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HurwitzApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HurwitzApproximationTasteGate_single_carrier_alignment_round_trip y)))

instance HurwitzApproximationTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier HurwitzApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := HurwitzApproximationTasteGate_single_carrier_alignment_fromEventFlow

instance HurwitzApproximationTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate HurwitzApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      HurwitzApproximationTasteGate_single_carrier_alignment_fromEventFlow
        (HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact HurwitzApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HurwitzApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def HurwitzApproximationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HurwitzApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  HurwitzApproximationTasteGate_single_carrier_alignment_ChapterTasteGate

theorem HurwitzApproximationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      HurwitzApproximationTasteGate_single_carrier_alignment_decodeBHist
        (HurwitzApproximationTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      HurwitzApproximationTasteGate_single_carrier_alignment_fields
          (HurwitzApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact HurwitzApproximationTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.HurwitzApproximationUp
