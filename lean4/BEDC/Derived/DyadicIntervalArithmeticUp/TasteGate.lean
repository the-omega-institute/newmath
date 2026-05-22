import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalArithmeticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalArithmeticUp : Type where
  | mk (L U O addDelta mulDelta R E H C P N : BHist) : DyadicIntervalArithmeticUp
  deriving DecidableEq

def dyadicIntervalArithmeticEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalArithmeticEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalArithmeticEncodeBHist h

def dyadicIntervalArithmeticDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalArithmeticDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalArithmeticDecodeBHist tail)

private theorem dyadicIntervalArithmeticDecode_encode :
    ∀ h : BHist,
      dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalArithmeticToEventFlow : DyadicIntervalArithmeticUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalArithmeticUp.mk L U O addDelta mulDelta R E H C P N =>
      [dyadicIntervalArithmeticEncodeBHist L, dyadicIntervalArithmeticEncodeBHist U,
        dyadicIntervalArithmeticEncodeBHist O, dyadicIntervalArithmeticEncodeBHist addDelta,
        dyadicIntervalArithmeticEncodeBHist mulDelta, dyadicIntervalArithmeticEncodeBHist R,
        dyadicIntervalArithmeticEncodeBHist E, dyadicIntervalArithmeticEncodeBHist H,
        dyadicIntervalArithmeticEncodeBHist C, dyadicIntervalArithmeticEncodeBHist P,
        dyadicIntervalArithmeticEncodeBHist N]

private def dyadicIntervalArithmeticEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalArithmeticEventAt index rest

def dyadicIntervalArithmeticFromEventFlow (ef : EventFlow) :
    Option DyadicIntervalArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalArithmeticUp.mk
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 0 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 1 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 2 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 3 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 4 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 5 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 6 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 7 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 8 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 9 ef))
      (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEventAt 10 ef)))

private theorem dyadicIntervalArithmetic_round_trip :
    ∀ x : DyadicIntervalArithmeticUp,
      dyadicIntervalArithmeticFromEventFlow (dyadicIntervalArithmeticToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U O addDelta mulDelta R E H C P N =>
      change
        some
            (DyadicIntervalArithmeticUp.mk
              (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist L))
              (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist U))
              (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist O))
              (dyadicIntervalArithmeticDecodeBHist
                (dyadicIntervalArithmeticEncodeBHist addDelta))
              (dyadicIntervalArithmeticDecodeBHist
                (dyadicIntervalArithmeticEncodeBHist mulDelta))
              (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist R))
              (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist E))
              (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist H))
              (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist C))
              (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist P))
              (dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist N))) =
          some (DyadicIntervalArithmeticUp.mk L U O addDelta mulDelta R E H C P N)
      rw [dyadicIntervalArithmeticDecode_encode L, dyadicIntervalArithmeticDecode_encode U,
        dyadicIntervalArithmeticDecode_encode O, dyadicIntervalArithmeticDecode_encode addDelta,
        dyadicIntervalArithmeticDecode_encode mulDelta, dyadicIntervalArithmeticDecode_encode R,
        dyadicIntervalArithmeticDecode_encode E, dyadicIntervalArithmeticDecode_encode H,
        dyadicIntervalArithmeticDecode_encode C, dyadicIntervalArithmeticDecode_encode P,
        dyadicIntervalArithmeticDecode_encode N]

private theorem dyadicIntervalArithmeticToEventFlow_injective
    {x y : DyadicIntervalArithmeticUp} :
    dyadicIntervalArithmeticToEventFlow x = dyadicIntervalArithmeticToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalArithmeticFromEventFlow (dyadicIntervalArithmeticToEventFlow x) =
        dyadicIntervalArithmeticFromEventFlow (dyadicIntervalArithmeticToEventFlow y) :=
    congrArg dyadicIntervalArithmeticFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicIntervalArithmetic_round_trip x).symm
      (Eq.trans hread (dyadicIntervalArithmetic_round_trip y)))

instance dyadicIntervalArithmeticBHistCarrier :
    BHistCarrier DyadicIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalArithmeticToEventFlow
  fromEventFlow := dyadicIntervalArithmeticFromEventFlow

instance dyadicIntervalArithmeticChapterTasteGate :
    ChapterTasteGate DyadicIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicIntervalArithmeticFromEventFlow (dyadicIntervalArithmeticToEventFlow x) = some x
    exact dyadicIntervalArithmetic_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicIntervalArithmeticToEventFlow_injective heq)

theorem DyadicIntervalArithmeticTasteGate_single_carrier_alignment :
    (forall h : BHist,
      dyadicIntervalArithmeticDecodeBHist (dyadicIntervalArithmeticEncodeBHist h) = h) ∧
      (forall x : DyadicIntervalArithmeticUp,
        dyadicIntervalArithmeticFromEventFlow (dyadicIntervalArithmeticToEventFlow x) =
          some x) ∧
        dyadicIntervalArithmeticEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicIntervalArithmeticDecode_encode
  · constructor
    · exact dyadicIntervalArithmetic_round_trip
    · rfl

end BEDC.Derived.DyadicIntervalArithmeticUp
