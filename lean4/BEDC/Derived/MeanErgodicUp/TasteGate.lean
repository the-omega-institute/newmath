import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MeanErgodicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MeanErgodicUp : Type where
  | mk (E D W T H A P R C Q N : BHist) : MeanErgodicUp
  deriving DecidableEq

def meanErgodicEncodeBHist : BHist -> RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: meanErgodicEncodeBHist h
  | BHist.e1 h => BMark.b1 :: meanErgodicEncodeBHist h

def meanErgodicDecodeBHist : RawEvent -> BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (meanErgodicDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (meanErgodicDecodeBHist tail)

private theorem MeanErgodicTasteGate_single_carrier_alignment_decode :
    forall h : BHist, meanErgodicDecodeBHist (meanErgodicEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def meanErgodicFields : MeanErgodicUp -> List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MeanErgodicUp.mk E D W T H A P R C Q N => [E, D, W, T, H, A, P, R, C, Q, N]

def meanErgodicToEventFlow : MeanErgodicUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => List.map meanErgodicEncodeBHist (meanErgodicFields x)

private def meanErgodicEventAt : Nat -> EventFlow -> RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => meanErgodicEventAt index rest

def meanErgodicFromEventFlow : EventFlow -> Option MeanErgodicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MeanErgodicUp.mk
        (meanErgodicDecodeBHist (meanErgodicEventAt 0 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 1 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 2 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 3 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 4 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 5 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 6 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 7 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 8 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 9 ef))
        (meanErgodicDecodeBHist (meanErgodicEventAt 10 ef)))

private theorem MeanErgodicTasteGate_single_carrier_alignment_round_trip :
    forall x : MeanErgodicUp, meanErgodicFromEventFlow (meanErgodicToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E D W T H A P R C Q N =>
      change
        some
            (MeanErgodicUp.mk
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist E))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist D))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist W))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist T))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist H))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist A))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist P))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist R))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist C))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist Q))
              (meanErgodicDecodeBHist (meanErgodicEncodeBHist N))) =
          some (MeanErgodicUp.mk E D W T H A P R C Q N)
      rw [MeanErgodicTasteGate_single_carrier_alignment_decode E,
        MeanErgodicTasteGate_single_carrier_alignment_decode D,
        MeanErgodicTasteGate_single_carrier_alignment_decode W,
        MeanErgodicTasteGate_single_carrier_alignment_decode T,
        MeanErgodicTasteGate_single_carrier_alignment_decode H,
        MeanErgodicTasteGate_single_carrier_alignment_decode A,
        MeanErgodicTasteGate_single_carrier_alignment_decode P,
        MeanErgodicTasteGate_single_carrier_alignment_decode R,
        MeanErgodicTasteGate_single_carrier_alignment_decode C,
        MeanErgodicTasteGate_single_carrier_alignment_decode Q,
        MeanErgodicTasteGate_single_carrier_alignment_decode N]

private theorem meanErgodicToEventFlow_injective {x y : MeanErgodicUp} :
    meanErgodicToEventFlow x = meanErgodicToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x = meanErgodicFromEventFlow (meanErgodicToEventFlow x) :=
        (MeanErgodicTasteGate_single_carrier_alignment_round_trip x).symm
      _ = meanErgodicFromEventFlow (meanErgodicToEventFlow y) :=
        congrArg meanErgodicFromEventFlow hxy
      _ = some y := MeanErgodicTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj hsome

instance meanErgodicBHistCarrier : BHistCarrier MeanErgodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := meanErgodicToEventFlow
  fromEventFlow := meanErgodicFromEventFlow

instance meanErgodicChapterTasteGate : ChapterTasteGate MeanErgodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change meanErgodicFromEventFlow (meanErgodicToEventFlow x) = some x
    exact MeanErgodicTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (meanErgodicToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MeanErgodicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  meanErgodicChapterTasteGate

theorem MeanErgodicTasteGate_single_carrier_alignment :
    (forall h : BHist, meanErgodicDecodeBHist (meanErgodicEncodeBHist h) = h) /\
      (forall x : MeanErgodicUp,
        meanErgodicFromEventFlow (meanErgodicToEventFlow x) = some x) /\
        (forall x y : MeanErgodicUp, meanErgodicToEventFlow x = meanErgodicToEventFlow y -> x = y) /\
          meanErgodicEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MeanErgodicTasteGate_single_carrier_alignment_decode,
      MeanErgodicTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact meanErgodicToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.MeanErgodicUp
