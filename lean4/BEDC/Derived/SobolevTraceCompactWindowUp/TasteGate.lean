import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevTraceCompactWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SobolevTraceCompactWindowUp : Type where
  | mk (K B S Q D E H C P N : BHist) : SobolevTraceCompactWindowUp
  deriving DecidableEq

def sobolevTraceCompactWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevTraceCompactWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevTraceCompactWindowEncodeBHist h

def sobolevTraceCompactWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevTraceCompactWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevTraceCompactWindowDecodeBHist tail)

private theorem sobolevTraceCompactWindow_decode_encode_bhist :
    ∀ h : BHist,
      sobolevTraceCompactWindowDecodeBHist
          (sobolevTraceCompactWindowEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sobolevTraceCompactWindowFields : SobolevTraceCompactWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevTraceCompactWindowUp.mk K B S Q D E H C P N =>
      [K, B, S, Q, D, E, H, C, P, N]

def sobolevTraceCompactWindowToEventFlow : SobolevTraceCompactWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sobolevTraceCompactWindowFields x).map sobolevTraceCompactWindowEncodeBHist

private def sobolevTraceCompactWindowEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sobolevTraceCompactWindowEventAt index rest

def sobolevTraceCompactWindowFromEventFlow
    (flow : EventFlow) : Option SobolevTraceCompactWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SobolevTraceCompactWindowUp.mk
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 0 flow))
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 1 flow))
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 2 flow))
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 3 flow))
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 4 flow))
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 5 flow))
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 6 flow))
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 7 flow))
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 8 flow))
      (sobolevTraceCompactWindowDecodeBHist (sobolevTraceCompactWindowEventAt 9 flow)))

private theorem sobolevTraceCompactWindow_round_trip :
    ∀ x : SobolevTraceCompactWindowUp,
      sobolevTraceCompactWindowFromEventFlow
          (sobolevTraceCompactWindowToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K B S Q D E H C P N =>
      change
        some
            (SobolevTraceCompactWindowUp.mk
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist K))
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist B))
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist S))
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist Q))
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist D))
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist E))
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist H))
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist C))
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist P))
              (sobolevTraceCompactWindowDecodeBHist
                (sobolevTraceCompactWindowEncodeBHist N))) =
          some (SobolevTraceCompactWindowUp.mk K B S Q D E H C P N)
      rw [sobolevTraceCompactWindow_decode_encode_bhist K,
        sobolevTraceCompactWindow_decode_encode_bhist B,
        sobolevTraceCompactWindow_decode_encode_bhist S,
        sobolevTraceCompactWindow_decode_encode_bhist Q,
        sobolevTraceCompactWindow_decode_encode_bhist D,
        sobolevTraceCompactWindow_decode_encode_bhist E,
        sobolevTraceCompactWindow_decode_encode_bhist H,
        sobolevTraceCompactWindow_decode_encode_bhist C,
        sobolevTraceCompactWindow_decode_encode_bhist P,
        sobolevTraceCompactWindow_decode_encode_bhist N]

private theorem sobolevTraceCompactWindowToEventFlow_injective
    {x y : SobolevTraceCompactWindowUp} :
    sobolevTraceCompactWindowToEventFlow x = sobolevTraceCompactWindowToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevTraceCompactWindowFromEventFlow (sobolevTraceCompactWindowToEventFlow x) =
        sobolevTraceCompactWindowFromEventFlow (sobolevTraceCompactWindowToEventFlow y) :=
    congrArg sobolevTraceCompactWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sobolevTraceCompactWindow_round_trip x).symm
      (Eq.trans hread (sobolevTraceCompactWindow_round_trip y)))

instance sobolevTraceCompactWindowBHistCarrier :
    BHistCarrier SobolevTraceCompactWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sobolevTraceCompactWindowToEventFlow
  fromEventFlow := sobolevTraceCompactWindowFromEventFlow

instance sobolevTraceCompactWindowChapterTasteGate :
    ChapterTasteGate SobolevTraceCompactWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sobolevTraceCompactWindowFromEventFlow
          (sobolevTraceCompactWindowToEventFlow x) =
        some x
    exact sobolevTraceCompactWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sobolevTraceCompactWindowToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SobolevTraceCompactWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sobolevTraceCompactWindowChapterTasteGate

theorem SobolevTraceCompactWindowTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SobolevTraceCompactWindowUp) ∧
      Nonempty (ChapterTasteGate SobolevTraceCompactWindowUp) ∧
        (∀ h : BHist,
          sobolevTraceCompactWindowDecodeBHist
              (sobolevTraceCompactWindowEncodeBHist h) =
            h) ∧
          (∀ x : SobolevTraceCompactWindowUp,
            sobolevTraceCompactWindowFromEventFlow
                (sobolevTraceCompactWindowToEventFlow x) =
              some x) ∧
            sobolevTraceCompactWindowEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨sobolevTraceCompactWindowBHistCarrier⟩
  constructor
  · exact ⟨sobolevTraceCompactWindowChapterTasteGate⟩
  constructor
  · exact sobolevTraceCompactWindow_decode_encode_bhist
  constructor
  · exact sobolevTraceCompactWindow_round_trip
  · rfl

end BEDC.Derived.SobolevTraceCompactWindowUp
