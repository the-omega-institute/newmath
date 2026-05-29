import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRootCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRootCriterionUp : Type where
  | mk (A Q W D T R E H C P N : BHist) : CauchyRootCriterionUp
  deriving DecidableEq

def cauchyRootCriterionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRootCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRootCriterionEncodeBHist h

def cauchyRootCriterionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRootCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRootCriterionDecodeBHist tail)

private theorem cauchyRootCriterionDecodeEncode :
    forall h : BHist, cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyRootCriterionFields : CauchyRootCriterionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRootCriterionUp.mk A Q W D T R E H C P N =>
      [A, Q, W, D, T, R, E, H, C, P, N]

def cauchyRootCriterionToEventFlow : CauchyRootCriterionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRootCriterionFields x).map cauchyRootCriterionEncodeBHist

def cauchyRootCriterionFromEventFlow : EventFlow -> Option CauchyRootCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [A, Q, W, D, T, R, E, H, C, P, N] =>
      some
        (CauchyRootCriterionUp.mk
          (cauchyRootCriterionDecodeBHist A)
          (cauchyRootCriterionDecodeBHist Q)
          (cauchyRootCriterionDecodeBHist W)
          (cauchyRootCriterionDecodeBHist D)
          (cauchyRootCriterionDecodeBHist T)
          (cauchyRootCriterionDecodeBHist R)
          (cauchyRootCriterionDecodeBHist E)
          (cauchyRootCriterionDecodeBHist H)
          (cauchyRootCriterionDecodeBHist C)
          (cauchyRootCriterionDecodeBHist P)
          (cauchyRootCriterionDecodeBHist N))
  | _ => none

private theorem cauchyRootCriterionRoundTrip :
    forall x : CauchyRootCriterionUp,
      cauchyRootCriterionFromEventFlow (cauchyRootCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Q W D T R E H C P N =>
      change
        some
          (CauchyRootCriterionUp.mk
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist A))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist Q))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist W))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist D))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist T))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist R))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist E))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist H))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist C))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist P))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist N))) =
          some (CauchyRootCriterionUp.mk A Q W D T R E H C P N)
      rw [cauchyRootCriterionDecodeEncode A, cauchyRootCriterionDecodeEncode Q,
        cauchyRootCriterionDecodeEncode W, cauchyRootCriterionDecodeEncode D,
        cauchyRootCriterionDecodeEncode T, cauchyRootCriterionDecodeEncode R,
        cauchyRootCriterionDecodeEncode E, cauchyRootCriterionDecodeEncode H,
        cauchyRootCriterionDecodeEncode C, cauchyRootCriterionDecodeEncode P,
        cauchyRootCriterionDecodeEncode N]

private theorem cauchyRootCriterionToEventFlow_injective {x y : CauchyRootCriterionUp} :
    cauchyRootCriterionToEventFlow x = cauchyRootCriterionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRootCriterionFromEventFlow (cauchyRootCriterionToEventFlow x) =
        cauchyRootCriterionFromEventFlow (cauchyRootCriterionToEventFlow y) :=
    congrArg cauchyRootCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRootCriterionRoundTrip x).symm
      (Eq.trans hread (cauchyRootCriterionRoundTrip y)))

instance cauchyRootCriterionBHistCarrier : BHistCarrier CauchyRootCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRootCriterionToEventFlow
  fromEventFlow := cauchyRootCriterionFromEventFlow

instance cauchyRootCriterionChapterTasteGateInstance :
    ChapterTasteGate CauchyRootCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRootCriterionFromEventFlow (cauchyRootCriterionToEventFlow x) = some x
    exact cauchyRootCriterionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRootCriterionToEventFlow_injective heq)

namespace TasteGate

theorem CauchyRootCriterionTasteGate_single_carrier_alignment :
    (forall A Q W D T R E H C P N : BHist,
      cauchyRootCriterionFields (CauchyRootCriterionUp.mk A Q W D T R E H C P N) =
        [A, Q, W, D, T, R, E, H, C, P, N]) ∧
      cauchyRootCriterionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨by intro A Q W D T R E H C P N; rfl, rfl⟩

end TasteGate

end BEDC.Derived.CauchyRootCriterionUp
