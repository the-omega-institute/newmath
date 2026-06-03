import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyBoundednessCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyBoundednessCriterionUp : Type where
  | mk (S B W R D E H C P N : BHist) : CauchyBoundednessCriterionUp
  deriving DecidableEq

def cauchyBoundednessCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyBoundednessCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyBoundednessCriterionEncodeBHist h

def cauchyBoundednessCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyBoundednessCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyBoundednessCriterionDecodeBHist tail)

private theorem cauchyBoundednessCriterionDecodeEncode :
    ∀ h : BHist,
      cauchyBoundednessCriterionDecodeBHist
          (cauchyBoundednessCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyBoundednessCriterionFields :
    CauchyBoundednessCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyBoundednessCriterionUp.mk S B W R D E H C P N =>
      [S, B, W, R, D, E, H, C, P, N]

def cauchyBoundednessCriterionToEventFlow :
    CauchyBoundednessCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyBoundednessCriterionFields x).map
      cauchyBoundednessCriterionEncodeBHist

private def cauchyBoundednessCriterionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyBoundednessCriterionEventAtDefault index rest

def cauchyBoundednessCriterionFromEventFlow
    (ef : EventFlow) : Option CauchyBoundednessCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyBoundednessCriterionUp.mk
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 0 ef))
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 1 ef))
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 2 ef))
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 3 ef))
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 4 ef))
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 5 ef))
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 6 ef))
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 7 ef))
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 8 ef))
      (cauchyBoundednessCriterionDecodeBHist
        (cauchyBoundednessCriterionEventAtDefault 9 ef)))

private theorem cauchyBoundednessCriterionRoundTrip :
    ∀ x : CauchyBoundednessCriterionUp,
      cauchyBoundednessCriterionFromEventFlow
          (cauchyBoundednessCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B W R D E H C P N =>
      change
        some
          (CauchyBoundednessCriterionUp.mk
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist S))
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist B))
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist W))
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist R))
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist D))
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist E))
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist H))
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist C))
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist P))
            (cauchyBoundednessCriterionDecodeBHist
              (cauchyBoundednessCriterionEncodeBHist N))) =
          some (CauchyBoundednessCriterionUp.mk S B W R D E H C P N)
      rw [cauchyBoundednessCriterionDecodeEncode S,
        cauchyBoundednessCriterionDecodeEncode B,
        cauchyBoundednessCriterionDecodeEncode W,
        cauchyBoundednessCriterionDecodeEncode R,
        cauchyBoundednessCriterionDecodeEncode D,
        cauchyBoundednessCriterionDecodeEncode E,
        cauchyBoundednessCriterionDecodeEncode H,
        cauchyBoundednessCriterionDecodeEncode C,
        cauchyBoundednessCriterionDecodeEncode P,
        cauchyBoundednessCriterionDecodeEncode N]

private theorem cauchyBoundednessCriterionToEventFlow_injective
    {x y : CauchyBoundednessCriterionUp} :
    cauchyBoundednessCriterionToEventFlow x =
        cauchyBoundednessCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyBoundednessCriterionFromEventFlow
          (cauchyBoundednessCriterionToEventFlow x) =
        cauchyBoundednessCriterionFromEventFlow
          (cauchyBoundednessCriterionToEventFlow y) :=
    congrArg cauchyBoundednessCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyBoundednessCriterionRoundTrip x).symm
      (Eq.trans hread (cauchyBoundednessCriterionRoundTrip y)))

instance cauchyBoundednessCriterionBHistCarrier :
    BHistCarrier CauchyBoundednessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyBoundednessCriterionToEventFlow
  fromEventFlow := cauchyBoundednessCriterionFromEventFlow

instance cauchyBoundednessCriterionChapterTasteGate :
    ChapterTasteGate CauchyBoundednessCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyBoundednessCriterionFromEventFlow
          (cauchyBoundednessCriterionToEventFlow x) =
        some x
    exact cauchyBoundednessCriterionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyBoundednessCriterionToEventFlow_injective heq)

theorem CauchyBoundednessCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyBoundednessCriterionDecodeBHist
          (cauchyBoundednessCriterionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CauchyBoundednessCriterionUp) ∧
        Nonempty (ChapterTasteGate CauchyBoundednessCriterionUp) ∧
          cauchyBoundednessCriterionEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyBoundednessCriterionDecodeEncode,
      ⟨cauchyBoundednessCriterionBHistCarrier⟩,
      ⟨cauchyBoundednessCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyBoundednessCriterionUp
