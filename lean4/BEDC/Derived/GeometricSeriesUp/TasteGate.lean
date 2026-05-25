import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeometricSeriesUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GeometricSeriesUp : Type where
  | mk (a q n W T R E H C P N : BHist) : GeometricSeriesUp
  deriving DecidableEq

def geometricSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: geometricSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: geometricSeriesEncodeBHist h

def geometricSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (geometricSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (geometricSeriesDecodeBHist tail)

private theorem geometricSeriesDecode_encode_bhist :
    ∀ h : BHist, geometricSeriesDecodeBHist (geometricSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def geometricSeriesFields : GeometricSeriesUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GeometricSeriesUp.mk a q n W T R E H C P N =>
      [a, q, n, W, T, R, E, H, C, P, N]

def geometricSeriesToEventFlow : GeometricSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (geometricSeriesFields x).map geometricSeriesEncodeBHist

private def geometricSeriesEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => geometricSeriesEventAtDefault index rest

def geometricSeriesFromEventFlow (ef : EventFlow) : Option GeometricSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GeometricSeriesUp.mk
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 0 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 1 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 2 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 3 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 4 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 5 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 6 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 7 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 8 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 9 ef))
      (geometricSeriesDecodeBHist (geometricSeriesEventAtDefault 10 ef)))

private theorem geometricSeries_round_trip :
    ∀ x : GeometricSeriesUp,
      geometricSeriesFromEventFlow (geometricSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a q n W T R E H C P N =>
      change
        some
          (GeometricSeriesUp.mk
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist a))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist q))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist n))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist W))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist T))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist R))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist E))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist H))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist C))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist P))
            (geometricSeriesDecodeBHist (geometricSeriesEncodeBHist N))) =
          some (GeometricSeriesUp.mk a q n W T R E H C P N)
      rw [geometricSeriesDecode_encode_bhist a,
        geometricSeriesDecode_encode_bhist q,
        geometricSeriesDecode_encode_bhist n,
        geometricSeriesDecode_encode_bhist W,
        geometricSeriesDecode_encode_bhist T,
        geometricSeriesDecode_encode_bhist R,
        geometricSeriesDecode_encode_bhist E,
        geometricSeriesDecode_encode_bhist H,
        geometricSeriesDecode_encode_bhist C,
        geometricSeriesDecode_encode_bhist P,
        geometricSeriesDecode_encode_bhist N]

private theorem geometricSeriesToEventFlow_injective {x y : GeometricSeriesUp} :
    geometricSeriesToEventFlow x = geometricSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      geometricSeriesFromEventFlow (geometricSeriesToEventFlow x) =
        geometricSeriesFromEventFlow (geometricSeriesToEventFlow y) :=
    congrArg geometricSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (geometricSeries_round_trip x).symm
      (Eq.trans hread (geometricSeries_round_trip y)))

instance geometricSeriesBHistCarrier : BHistCarrier GeometricSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := geometricSeriesToEventFlow
  fromEventFlow := geometricSeriesFromEventFlow

instance geometricSeriesChapterTasteGate : ChapterTasteGate GeometricSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change geometricSeriesFromEventFlow (geometricSeriesToEventFlow x) = some x
    exact geometricSeries_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (geometricSeriesToEventFlow_injective heq)

theorem GeometricSeriesTasteGate_single_carrier_alignment :
    (∀ h : BHist, geometricSeriesDecodeBHist
      (geometricSeriesEncodeBHist h) = h) ∧
      (∀ x : GeometricSeriesUp,
        geometricSeriesFromEventFlow
          (geometricSeriesToEventFlow x) = some x) ∧
        (∀ x y : GeometricSeriesUp,
          geometricSeriesToEventFlow x =
            geometricSeriesToEventFlow y → x = y) ∧
          geometricSeriesEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact geometricSeriesDecode_encode_bhist
  · constructor
    · exact geometricSeries_round_trip
    · constructor
      · intro x y heq
        exact geometricSeriesToEventFlow_injective heq
      · rfl

end BEDC.Derived.GeometricSeriesUp.TasteGate
