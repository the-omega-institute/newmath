import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealBoundedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealBoundedIntervalUp : Type where
  | mk (L U D S T R Q B H C P N : BHist) : RealBoundedIntervalUp
  deriving DecidableEq

def realBoundedIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realBoundedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realBoundedIntervalEncodeBHist h

def realBoundedIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realBoundedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realBoundedIntervalDecodeBHist tail)

private theorem RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def realBoundedIntervalFields : RealBoundedIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealBoundedIntervalUp.mk L U D S T R Q B H C P N =>
      [L, U, D, S, T, R, Q, B, H, C, P, N]

def realBoundedIntervalToEventFlow : RealBoundedIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realBoundedIntervalFields x).map realBoundedIntervalEncodeBHist

private def realBoundedIntervalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realBoundedIntervalEventAt index rest

def realBoundedIntervalFromEventFlow (ef : EventFlow) :
    Option RealBoundedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealBoundedIntervalUp.mk
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 0 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 1 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 2 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 3 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 4 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 5 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 6 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 7 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 8 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 9 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 10 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 11 ef)))

private theorem RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip
    (x : RealBoundedIntervalUp) :
    realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U D S T R Q B H C P N =>
      change
        some
          (RealBoundedIntervalUp.mk
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist L))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist U))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist D))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist S))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist T))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist R))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist Q))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist B))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist H))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist C))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist P))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist N))) =
          some (RealBoundedIntervalUp.mk L U D S T R Q B H C P N)
      rw [RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode L,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode U,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode D,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode S,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode T,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode R,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode Q,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode B,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode H,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode C,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode P,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealBoundedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealBoundedIntervalUp} :
    realBoundedIntervalToEventFlow x = realBoundedIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow x) =
        realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow y) :=
    congrArg realBoundedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance realBoundedIntervalBHistCarrier : BHistCarrier RealBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realBoundedIntervalToEventFlow
  fromEventFlow := realBoundedIntervalFromEventFlow

instance realBoundedIntervalChapterTasteGate :
    ChapterTasteGate RealBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow x) = some x
    exact RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealBoundedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RealBoundedIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist h) = h) ∧
      (∀ x : RealBoundedIntervalUp,
        realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow x) = some x) ∧
      (∀ x y : RealBoundedIntervalUp,
        realBoundedIntervalToEventFlow x = realBoundedIntervalToEventFlow y → x = y) ∧
      realBoundedIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact RealBoundedIntervalTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y
    exact RealBoundedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
  · rfl

end BEDC.Derived.RealBoundedIntervalUp
