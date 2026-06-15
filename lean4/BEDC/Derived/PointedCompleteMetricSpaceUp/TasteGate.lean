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
      pointedCompleteMetricSpaceDecodeBHist (pointedCompleteMetricSpaceEncodeBHist h) =
        h := by
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

def pointedCompleteMetricSpaceSplitEventFlow :
    EventFlow →
      Option
        (RawEvent × RawEvent × RawEvent × RawEvent × RawEvent × RawEvent × RawEvent ×
          RawEvent × RawEvent × RawEvent × RawEvent)
  -- BEDC touchpoint anchor: BHist BMark
  | m :: b :: q :: s :: r :: e :: l :: h :: c :: p0 :: n :: [] =>
      some (m, b, q, s, r, e, l, h, c, p0, n)
  | _ => none

def pointedCompleteMetricSpaceFromEventFlow
    (ef : EventFlow) : Option PointedCompleteMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match pointedCompleteMetricSpaceSplitEventFlow ef with
  | some (m, b, q, s, r, e, l, h, c, p0, n) =>
      some
        (PointedCompleteMetricSpaceUp.mk
          (pointedCompleteMetricSpaceDecodeBHist m)
          (pointedCompleteMetricSpaceDecodeBHist b)
          (pointedCompleteMetricSpaceDecodeBHist q)
          (pointedCompleteMetricSpaceDecodeBHist s)
          (pointedCompleteMetricSpaceDecodeBHist r)
          (pointedCompleteMetricSpaceDecodeBHist e)
          (pointedCompleteMetricSpaceDecodeBHist l)
          (pointedCompleteMetricSpaceDecodeBHist h)
          (pointedCompleteMetricSpaceDecodeBHist c)
          (pointedCompleteMetricSpaceDecodeBHist p0)
          (pointedCompleteMetricSpaceDecodeBHist n))
  | none => none

private theorem pointedCompleteMetricSpace_round_trip :
    ∀ x : PointedCompleteMetricSpaceUp,
      pointedCompleteMetricSpaceFromEventFlow
          (pointedCompleteMetricSpaceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M B Q S R E L H C P0 N =>
      change
        some
            (PointedCompleteMetricSpaceUp.mk
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist M))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist B))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist Q))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist S))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist R))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist E))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist L))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist H))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist C))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist P0))
              (pointedCompleteMetricSpaceDecodeBHist
                (pointedCompleteMetricSpaceEncodeBHist N))) =
          some (PointedCompleteMetricSpaceUp.mk M B Q S R E L H C P0 N)
      rw [pointedCompleteMetricSpace_decode_encode_bhist M]
      rw [pointedCompleteMetricSpace_decode_encode_bhist B]
      rw [pointedCompleteMetricSpace_decode_encode_bhist Q]
      rw [pointedCompleteMetricSpace_decode_encode_bhist S]
      rw [pointedCompleteMetricSpace_decode_encode_bhist R]
      rw [pointedCompleteMetricSpace_decode_encode_bhist E]
      rw [pointedCompleteMetricSpace_decode_encode_bhist L]
      rw [pointedCompleteMetricSpace_decode_encode_bhist H]
      rw [pointedCompleteMetricSpace_decode_encode_bhist C]
      rw [pointedCompleteMetricSpace_decode_encode_bhist P0]
      rw [pointedCompleteMetricSpace_decode_encode_bhist N]

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

instance pointedCompleteMetricSpaceBHistCarrier :
    BHistCarrier PointedCompleteMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pointedCompleteMetricSpaceToEventFlow
  fromEventFlow := pointedCompleteMetricSpaceFromEventFlow

instance pointedCompleteMetricSpaceChapterTasteGate :
    ChapterTasteGate PointedCompleteMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      pointedCompleteMetricSpaceFromEventFlow
          (pointedCompleteMetricSpaceToEventFlow x) =
        some x
    exact pointedCompleteMetricSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pointedCompleteMetricSpaceToEventFlow_injective heq)

end BEDC.Derived.PointedCompleteMetricSpaceUp
