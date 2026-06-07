import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyWindowStabilityBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyWindowStabilityBridgeUp : Type where
  | mk (S0 S1 T D R0 R1 E0 E1 H C P N : BHist) :
      CauchyWindowStabilityBridgeUp
  deriving DecidableEq

def cauchyWindowStabilityBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyWindowStabilityBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyWindowStabilityBridgeEncodeBHist h

def cauchyWindowStabilityBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyWindowStabilityBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyWindowStabilityBridgeDecodeBHist tail)

private theorem cauchyWindowStabilityBridge_decode_encode :
    ∀ h : BHist,
      cauchyWindowStabilityBridgeDecodeBHist
          (cauchyWindowStabilityBridgeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyWindowStabilityBridgeFields :
    CauchyWindowStabilityBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyWindowStabilityBridgeUp.mk S0 S1 T D R0 R1 E0 E1 H C P N =>
      [S0, S1, T, D, R0, R1, E0, E1, H, C, P, N]

def cauchyWindowStabilityBridgeToEventFlow :
    CauchyWindowStabilityBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map cauchyWindowStabilityBridgeEncodeBHist
        (cauchyWindowStabilityBridgeFields x)

private def cauchyWindowStabilityBridgeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyWindowStabilityBridgeRawAt index rest

def cauchyWindowStabilityBridgeFromEventFlow
    (flow : EventFlow) : Option CauchyWindowStabilityBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyWindowStabilityBridgeUp.mk
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 0 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 1 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 2 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 3 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 4 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 5 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 6 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 7 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 8 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 9 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 10 flow))
      (cauchyWindowStabilityBridgeDecodeBHist
        (cauchyWindowStabilityBridgeRawAt 11 flow)))

private theorem cauchyWindowStabilityBridge_round_trip :
    ∀ x : CauchyWindowStabilityBridgeUp,
      cauchyWindowStabilityBridgeFromEventFlow
          (cauchyWindowStabilityBridgeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 T D R0 R1 E0 E1 H C P N =>
      change
        some
          (CauchyWindowStabilityBridgeUp.mk
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist S0))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist S1))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist T))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist D))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist R0))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist R1))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist E0))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist E1))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist H))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist C))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist P))
            (cauchyWindowStabilityBridgeDecodeBHist
              (cauchyWindowStabilityBridgeEncodeBHist N))) =
          some (CauchyWindowStabilityBridgeUp.mk S0 S1 T D R0 R1 E0 E1 H C P N)
      rw [cauchyWindowStabilityBridge_decode_encode S0,
        cauchyWindowStabilityBridge_decode_encode S1,
        cauchyWindowStabilityBridge_decode_encode T,
        cauchyWindowStabilityBridge_decode_encode D,
        cauchyWindowStabilityBridge_decode_encode R0,
        cauchyWindowStabilityBridge_decode_encode R1,
        cauchyWindowStabilityBridge_decode_encode E0,
        cauchyWindowStabilityBridge_decode_encode E1,
        cauchyWindowStabilityBridge_decode_encode H,
        cauchyWindowStabilityBridge_decode_encode C,
        cauchyWindowStabilityBridge_decode_encode P,
        cauchyWindowStabilityBridge_decode_encode N]

private theorem cauchyWindowStabilityBridgeToEventFlow_injective
    {x y : CauchyWindowStabilityBridgeUp} :
    cauchyWindowStabilityBridgeToEventFlow x =
        cauchyWindowStabilityBridgeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyWindowStabilityBridgeFromEventFlow
          (cauchyWindowStabilityBridgeToEventFlow x) =
        cauchyWindowStabilityBridgeFromEventFlow
          (cauchyWindowStabilityBridgeToEventFlow y) :=
    congrArg cauchyWindowStabilityBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyWindowStabilityBridge_round_trip x).symm
      (Eq.trans hread (cauchyWindowStabilityBridge_round_trip y)))

instance cauchyWindowStabilityBridgeBHistCarrier :
    BHistCarrier CauchyWindowStabilityBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyWindowStabilityBridgeToEventFlow
  fromEventFlow := cauchyWindowStabilityBridgeFromEventFlow

instance cauchyWindowStabilityBridgeChapterTasteGate :
    ChapterTasteGate CauchyWindowStabilityBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyWindowStabilityBridgeFromEventFlow
          (cauchyWindowStabilityBridgeToEventFlow x) =
        some x
    exact cauchyWindowStabilityBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyWindowStabilityBridgeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyWindowStabilityBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyWindowStabilityBridgeChapterTasteGate

theorem CauchyWindowStabilityBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyWindowStabilityBridgeDecodeBHist
          (cauchyWindowStabilityBridgeEncodeBHist h) =
        h) ∧
      (∀ x : CauchyWindowStabilityBridgeUp,
        cauchyWindowStabilityBridgeFromEventFlow
            (cauchyWindowStabilityBridgeToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyWindowStabilityBridgeUp,
          cauchyWindowStabilityBridgeToEventFlow x =
              cauchyWindowStabilityBridgeToEventFlow y →
            x = y) ∧
          cauchyWindowStabilityBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyWindowStabilityBridge_decode_encode,
      cauchyWindowStabilityBridge_round_trip,
      by
        intro x y heq
        exact cauchyWindowStabilityBridgeToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyWindowStabilityBridgeUp
