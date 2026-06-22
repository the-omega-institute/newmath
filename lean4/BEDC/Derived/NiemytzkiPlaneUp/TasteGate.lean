import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NiemytzkiPlaneUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NiemytzkiPlaneUp : Type where
  | mk (U B T R Q H C P L : BHist) : NiemytzkiPlaneUp
  deriving DecidableEq

def niemytzkiPlaneEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: niemytzkiPlaneEncodeBHist h
  | BHist.e1 h => BMark.b1 :: niemytzkiPlaneEncodeBHist h

def niemytzkiPlaneDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (niemytzkiPlaneDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (niemytzkiPlaneDecodeBHist tail)

private theorem NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def niemytzkiPlaneFields : NiemytzkiPlaneUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NiemytzkiPlaneUp.mk U B T R Q H C P L => [U, B, T, R, Q, H, C, P, L]

def niemytzkiPlaneToEventFlow : NiemytzkiPlaneUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (niemytzkiPlaneFields x).map niemytzkiPlaneEncodeBHist

private def niemytzkiPlaneEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => niemytzkiPlaneEventAt index rest

def niemytzkiPlaneFromEventFlow (ef : EventFlow) : Option NiemytzkiPlaneUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NiemytzkiPlaneUp.mk
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 0 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 1 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 2 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 3 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 4 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 5 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 6 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 7 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 8 ef)))

private theorem NiemytzkiPlaneTasteGate_single_carrier_alignment_round_trip
    (x : NiemytzkiPlaneUp) :
    niemytzkiPlaneFromEventFlow (niemytzkiPlaneToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U B T R Q H C P L =>
      change
        some
          (NiemytzkiPlaneUp.mk
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist U))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist B))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist T))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist R))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist Q))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist H))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist C))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist P))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist L))) =
          some (NiemytzkiPlaneUp.mk U B T R Q H C P L)
      rw [NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode U,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode B,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode T,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode R,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode Q,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode H,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode C,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode P,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode L]

private theorem NiemytzkiPlaneToEventFlow_injective {x y : NiemytzkiPlaneUp} :
    niemytzkiPlaneToEventFlow x = niemytzkiPlaneToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      niemytzkiPlaneFromEventFlow (niemytzkiPlaneToEventFlow x) =
        niemytzkiPlaneFromEventFlow (niemytzkiPlaneToEventFlow y) :=
    congrArg niemytzkiPlaneFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NiemytzkiPlaneTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NiemytzkiPlaneTasteGate_single_carrier_alignment_round_trip y)))

instance niemytzkiPlaneBHistCarrier : BHistCarrier NiemytzkiPlaneUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := niemytzkiPlaneToEventFlow
  fromEventFlow := niemytzkiPlaneFromEventFlow

instance niemytzkiPlaneChapterTasteGate : ChapterTasteGate NiemytzkiPlaneUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change niemytzkiPlaneFromEventFlow (niemytzkiPlaneToEventFlow x) = some x
    exact NiemytzkiPlaneTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NiemytzkiPlaneToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NiemytzkiPlaneUp :=
  -- BEDC touchpoint anchor: BHist BMark
  niemytzkiPlaneChapterTasteGate

theorem NiemytzkiPlaneTasteGate_single_carrier_alignment :
    (forall h : BHist, niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier NiemytzkiPlaneUp) ∧
        Nonempty (ChapterTasteGate NiemytzkiPlaneUp) ∧
          niemytzkiPlaneEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode,
      ⟨niemytzkiPlaneBHistCarrier⟩,
      ⟨niemytzkiPlaneChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.NiemytzkiPlaneUp
