import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GapClosureBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GapClosureBoundaryUp : Type where
  | mk :
      (gap source refusal transport continuation provenance name : BHist) →
      GapClosureBoundaryUp
  deriving DecidableEq

private def encodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist :
    ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def toEventFlow : GapClosureBoundaryUp → EventFlow
  | GapClosureBoundaryUp.mk gap source refusal transport continuation provenance name =>
      [[BMark.b0],
        encodeBHist gap,
        [BMark.b1, BMark.b0],
        encodeBHist source,
        [BMark.b1, BMark.b1, BMark.b0],
        encodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist name]

private def fromEventFlow : EventFlow → Option GapClosureBoundaryUp
  | _tag0 :: gap :: _tag1 :: source :: _tag2 :: refusal :: _tag3 :: transport ::
      _tag4 :: continuation :: _tag5 :: provenance :: _tag6 :: name :: [] =>
      some
        (GapClosureBoundaryUp.mk (decodeBHist gap) (decodeBHist source)
          (decodeBHist refusal) (decodeBHist transport) (decodeBHist continuation)
          (decodeBHist provenance) (decodeBHist name))
  | _ => none

instance bHistCarrier : BHistCarrier GapClosureBoundaryUp where
  toEventFlow := toEventFlow
  fromEventFlow := fromEventFlow

private theorem round_trip :
    ∀ x : GapClosureBoundaryUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  intro x
  cases x with
  | mk gap source refusal transport continuation provenance name =>
      simp [BHistCarrier.toEventFlow, BHistCarrier.fromEventFlow, toEventFlow, fromEventFlow,
        decode_encode_bhist]

private theorem toEventFlow_injective :
    ∀ x y : GapClosureBoundaryUp, toEventFlow x = toEventFlow y → x = y := by
  intro x y heq
  have hx : fromEventFlow (toEventFlow x) = some x := by
    exact round_trip x
  have hy : fromEventFlow (toEventFlow y) = some y := by
    exact round_trip y
  have hxy : some x = some y := by
    exact Eq.trans hx.symm (Eq.trans (congrArg fromEventFlow heq) hy)
  cases hxy
  rfl

def taste_gate : ChapterTasteGate GapClosureBoundaryUp where
  round_trip := round_trip
  layer_separation := by
    intro x y hxy heq
    apply hxy
    exact toEventFlow_injective x y heq

end BEDC.Derived.GapClosureBoundaryUp
