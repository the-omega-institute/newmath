import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpperSemicontinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpperSemicontinuousUp : Type where
  | mk (X F S W R O H C P N : BHist) : UpperSemicontinuousUp
  deriving DecidableEq

def upperSemicontinuousEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: upperSemicontinuousEncodeBHist h
  | BHist.e1 h => BMark.b1 :: upperSemicontinuousEncodeBHist h

def upperSemicontinuousDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (upperSemicontinuousDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (upperSemicontinuousDecodeBHist tail)

private theorem upperSemicontinuousDecode_encode :
    ∀ h : BHist, upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def upperSemicontinuousToEventFlow : UpperSemicontinuousUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UpperSemicontinuousUp.mk X F S W R O H C P N =>
      [upperSemicontinuousEncodeBHist X, upperSemicontinuousEncodeBHist F,
        upperSemicontinuousEncodeBHist S, upperSemicontinuousEncodeBHist W,
        upperSemicontinuousEncodeBHist R, upperSemicontinuousEncodeBHist O,
        upperSemicontinuousEncodeBHist H, upperSemicontinuousEncodeBHist C,
        upperSemicontinuousEncodeBHist P, upperSemicontinuousEncodeBHist N]

private def upperSemicontinuousEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => upperSemicontinuousEventAt index rest

def upperSemicontinuousFromEventFlow (ef : EventFlow) : Option UpperSemicontinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UpperSemicontinuousUp.mk
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 0 ef))
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 1 ef))
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 2 ef))
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 3 ef))
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 4 ef))
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 5 ef))
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 6 ef))
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 7 ef))
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 8 ef))
      (upperSemicontinuousDecodeBHist (upperSemicontinuousEventAt 9 ef)))

private theorem upperSemicontinuous_round_trip :
    ∀ x : UpperSemicontinuousUp,
      upperSemicontinuousFromEventFlow (upperSemicontinuousToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F S W R O H C P N =>
      change
        some
            (UpperSemicontinuousUp.mk
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist X))
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist F))
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist S))
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist W))
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist R))
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist O))
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist H))
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist C))
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist P))
              (upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist N))) =
          some (UpperSemicontinuousUp.mk X F S W R O H C P N)
      rw [upperSemicontinuousDecode_encode X, upperSemicontinuousDecode_encode F,
        upperSemicontinuousDecode_encode S, upperSemicontinuousDecode_encode W,
        upperSemicontinuousDecode_encode R, upperSemicontinuousDecode_encode O,
        upperSemicontinuousDecode_encode H, upperSemicontinuousDecode_encode C,
        upperSemicontinuousDecode_encode P, upperSemicontinuousDecode_encode N]

private theorem upperSemicontinuousToEventFlow_injective {x y : UpperSemicontinuousUp} :
    upperSemicontinuousToEventFlow x = upperSemicontinuousToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      upperSemicontinuousFromEventFlow (upperSemicontinuousToEventFlow x) =
        upperSemicontinuousFromEventFlow (upperSemicontinuousToEventFlow y) :=
    congrArg upperSemicontinuousFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (upperSemicontinuous_round_trip x).symm
      (Eq.trans hread (upperSemicontinuous_round_trip y)))

instance upperSemicontinuousBHistCarrier : BHistCarrier UpperSemicontinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := upperSemicontinuousToEventFlow
  fromEventFlow := upperSemicontinuousFromEventFlow

instance upperSemicontinuousChapterTasteGate : ChapterTasteGate UpperSemicontinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change upperSemicontinuousFromEventFlow (upperSemicontinuousToEventFlow x) = some x
    exact upperSemicontinuous_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (upperSemicontinuousToEventFlow_injective heq)

theorem UpperSemicontinuousTasteGate_single_carrier_alignment :
    (forall h : BHist,
      upperSemicontinuousDecodeBHist (upperSemicontinuousEncodeBHist h) = h) ∧
      (forall x : UpperSemicontinuousUp,
        upperSemicontinuousFromEventFlow (upperSemicontinuousToEventFlow x) = some x) ∧
        upperSemicontinuousEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact upperSemicontinuousDecode_encode
  · constructor
    · exact upperSemicontinuous_round_trip
    · rfl

end BEDC.Derived.UpperSemicontinuousUp
