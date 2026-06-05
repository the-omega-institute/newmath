import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealTightnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealTightnessUp : Type where
  | mk (R D S Q I B O T H C P N : BHist) : RealTightnessUp
  deriving DecidableEq

def realTightnessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realTightnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realTightnessEncodeBHist h

def realTightnessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realTightnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realTightnessDecodeBHist tail)

private theorem RealTightnessTasteGate_decode_encode :
    forall h : BHist, realTightnessDecodeBHist (realTightnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realTightnessFields : RealTightnessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealTightnessUp.mk R D S Q I B O T H C P N =>
      [R, D, S, Q, I, B, O, T, H, C, P, N]

def realTightnessToEventFlow : RealTightnessUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realTightnessFields x).map realTightnessEncodeBHist

private def realTightnessRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realTightnessRawAt index rest

private def realTightnessLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => realTightnessLengthEq index rest

def realTightnessFromEventFlow : EventFlow -> Option RealTightnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match realTightnessLengthEq 12 flow with
      | true =>
          some
            (RealTightnessUp.mk
              (realTightnessDecodeBHist (realTightnessRawAt 0 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 1 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 2 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 3 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 4 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 5 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 6 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 7 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 8 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 9 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 10 flow))
              (realTightnessDecodeBHist (realTightnessRawAt 11 flow)))
      | false => none

private theorem realTightness_round_trip :
    forall x : RealTightnessUp,
      realTightnessFromEventFlow (realTightnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R D S Q I B O T H C P N =>
      change
        some
          (RealTightnessUp.mk
            (realTightnessDecodeBHist (realTightnessEncodeBHist R))
            (realTightnessDecodeBHist (realTightnessEncodeBHist D))
            (realTightnessDecodeBHist (realTightnessEncodeBHist S))
            (realTightnessDecodeBHist (realTightnessEncodeBHist Q))
            (realTightnessDecodeBHist (realTightnessEncodeBHist I))
            (realTightnessDecodeBHist (realTightnessEncodeBHist B))
            (realTightnessDecodeBHist (realTightnessEncodeBHist O))
            (realTightnessDecodeBHist (realTightnessEncodeBHist T))
            (realTightnessDecodeBHist (realTightnessEncodeBHist H))
            (realTightnessDecodeBHist (realTightnessEncodeBHist C))
            (realTightnessDecodeBHist (realTightnessEncodeBHist P))
            (realTightnessDecodeBHist (realTightnessEncodeBHist N))) =
          some (RealTightnessUp.mk R D S Q I B O T H C P N)
      rw [RealTightnessTasteGate_decode_encode R, RealTightnessTasteGate_decode_encode D,
        RealTightnessTasteGate_decode_encode S, RealTightnessTasteGate_decode_encode Q,
        RealTightnessTasteGate_decode_encode I, RealTightnessTasteGate_decode_encode B,
        RealTightnessTasteGate_decode_encode O, RealTightnessTasteGate_decode_encode T,
        RealTightnessTasteGate_decode_encode H, RealTightnessTasteGate_decode_encode C,
        RealTightnessTasteGate_decode_encode P, RealTightnessTasteGate_decode_encode N]

private theorem realTightnessToEventFlow_injective {x y : RealTightnessUp} :
    realTightnessToEventFlow x = realTightnessToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realTightnessFromEventFlow (realTightnessToEventFlow x) =
        realTightnessFromEventFlow (realTightnessToEventFlow y) :=
    congrArg realTightnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realTightness_round_trip x).symm
      (Eq.trans hread (realTightness_round_trip y)))

instance realTightnessBHistCarrier : BHistCarrier RealTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realTightnessToEventFlow
  fromEventFlow := realTightnessFromEventFlow

instance realTightnessChapterTasteGate : ChapterTasteGate RealTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realTightnessFromEventFlow (realTightnessToEventFlow x) = some x
    exact realTightness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realTightnessToEventFlow_injective heq)

namespace TasteGate

theorem RealTightnessTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RealTightnessUp) ∧
      Nonempty (ChapterTasteGate RealTightnessUp) ∧
        realTightnessFields
            (RealTightnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨Nonempty.intro realTightnessBHistCarrier,
      Nonempty.intro realTightnessChapterTasteGate,
      rfl⟩

end TasteGate

end BEDC.Derived.RealTightnessUp
