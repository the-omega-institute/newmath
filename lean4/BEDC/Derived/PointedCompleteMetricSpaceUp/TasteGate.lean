import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PointedCompleteMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PointedCompleteMetricSpaceUp : Type where
  | mk (M B Q S R E L H C P0 N : BHist) : PointedCompleteMetricSpaceUp
  deriving DecidableEq

def pointedCompleteMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pointedCompleteMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pointedCompleteMetricSpaceEncodeBHist h

def pointedCompleteMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pointedCompleteMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pointedCompleteMetricSpaceDecodeBHist tail)

private theorem pointedCompleteMetricSpace_decode_encode_bhist :
    ∀ h : BHist,
      pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def pointedCompleteMetricSpaceFields : PointedCompleteMetricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PointedCompleteMetricSpaceUp.mk M B Q S R E L H C P0 N =>
      [M, B, Q, S, R, E, L, H, C, P0, N]

def pointedCompleteMetricSpaceToEventFlow : PointedCompleteMetricSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (pointedCompleteMetricSpaceFields x).map pointedCompleteMetricSpaceEncodeBHist

private def pointedCompleteMetricSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pointedCompleteMetricSpaceEventAtDefault index rest

def pointedCompleteMetricSpaceFromEventFlow
    (ef : EventFlow) : Option PointedCompleteMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PointedCompleteMetricSpaceUp.mk
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 0 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 1 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 2 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 3 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 4 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 5 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 6 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 7 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 8 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 9 ef))
      (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEventAtDefault 10 ef)))

private theorem pointedCompleteMetricSpace_round_trip :
    ∀ x : PointedCompleteMetricSpaceUp,
      pointedCompleteMetricSpaceFromEventFlow (pointedCompleteMetricSpaceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M B Q S R E L H C P0 N =>
      change
        some
          (PointedCompleteMetricSpaceUp.mk
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist M))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist B))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist Q))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist S))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist R))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist E))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist L))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist H))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist C))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist P0))
            (pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist N))) =
          some (PointedCompleteMetricSpaceUp.mk M B Q S R E L H C P0 N)
      rw [pointedCompleteMetricSpace_decode_encode_bhist M,
        pointedCompleteMetricSpace_decode_encode_bhist B,
        pointedCompleteMetricSpace_decode_encode_bhist Q,
        pointedCompleteMetricSpace_decode_encode_bhist S,
        pointedCompleteMetricSpace_decode_encode_bhist R,
        pointedCompleteMetricSpace_decode_encode_bhist E,
        pointedCompleteMetricSpace_decode_encode_bhist L,
        pointedCompleteMetricSpace_decode_encode_bhist H,
        pointedCompleteMetricSpace_decode_encode_bhist C,
        pointedCompleteMetricSpace_decode_encode_bhist P0,
        pointedCompleteMetricSpace_decode_encode_bhist N]

private theorem pointedCompleteMetricSpaceToEventFlow_injective
    {x y : PointedCompleteMetricSpaceUp} :
    pointedCompleteMetricSpaceToEventFlow x = pointedCompleteMetricSpaceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pointedCompleteMetricSpaceFromEventFlow (pointedCompleteMetricSpaceToEventFlow x) =
        pointedCompleteMetricSpaceFromEventFlow (pointedCompleteMetricSpaceToEventFlow y) :=
    congrArg pointedCompleteMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (pointedCompleteMetricSpace_round_trip x).symm
      (Eq.trans hread (pointedCompleteMetricSpace_round_trip y)))

private theorem pointedCompleteMetricSpace_field_faithful :
    ∀ x y : PointedCompleteMetricSpaceUp,
      pointedCompleteMetricSpaceFields x = pointedCompleteMetricSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ B₁ Q₁ S₁ R₁ E₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ B₂ Q₂ S₂ R₂ E₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance pointedCompleteMetricSpaceBHistCarrier : BHistCarrier PointedCompleteMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pointedCompleteMetricSpaceToEventFlow
  fromEventFlow := pointedCompleteMetricSpaceFromEventFlow

instance pointedCompleteMetricSpaceFieldFaithful : FieldFaithful PointedCompleteMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pointedCompleteMetricSpaceFields
  field_faithful := pointedCompleteMetricSpace_field_faithful

instance pointedCompleteMetricSpaceChapterTasteGate :
    ChapterTasteGate PointedCompleteMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      pointedCompleteMetricSpaceFromEventFlow (pointedCompleteMetricSpaceToEventFlow x) =
        some x
    exact pointedCompleteMetricSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pointedCompleteMetricSpaceToEventFlow_injective heq)

namespace TasteGate

def taste_gate : ChapterTasteGate PointedCompleteMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pointedCompleteMetricSpaceChapterTasteGate

theorem PointedCompleteMetricSpaceTasteGate_single_carrier_alignment :
    ChapterTasteGate PointedCompleteMetricSpaceUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact pointedCompleteMetricSpaceChapterTasteGate

end TasteGate

end BEDC.Derived.PointedCompleteMetricSpaceUp
