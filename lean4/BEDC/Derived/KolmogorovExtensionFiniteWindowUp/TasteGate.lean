import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KolmogorovExtensionFiniteWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KolmogorovExtensionFiniteWindowUp : Type where
  | mk (I W mu pi R H C P N : BHist) : KolmogorovExtensionFiniteWindowUp
  deriving DecidableEq

def kolmogorovExtensionFiniteWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kolmogorovExtensionFiniteWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kolmogorovExtensionFiniteWindowEncodeBHist h

def kolmogorovExtensionFiniteWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kolmogorovExtensionFiniteWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kolmogorovExtensionFiniteWindowDecodeBHist tail)

private theorem kolmogorovExtensionFiniteWindowDecode_encode :
    ∀ h : BHist,
      kolmogorovExtensionFiniteWindowDecodeBHist
          (kolmogorovExtensionFiniteWindowEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kolmogorovExtensionFiniteWindowFields :
    KolmogorovExtensionFiniteWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KolmogorovExtensionFiniteWindowUp.mk I W mu pi R H C P N => [I, W, mu, pi, R, H, C, P, N]

def kolmogorovExtensionFiniteWindowToEventFlow :
    KolmogorovExtensionFiniteWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kolmogorovExtensionFiniteWindowFields x).map kolmogorovExtensionFiniteWindowEncodeBHist

private def kolmogorovExtensionFiniteWindowEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kolmogorovExtensionFiniteWindowEventAtDefault index rest

def kolmogorovExtensionFiniteWindowFromEventFlow
    (ef : EventFlow) : Option KolmogorovExtensionFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KolmogorovExtensionFiniteWindowUp.mk
      (kolmogorovExtensionFiniteWindowDecodeBHist
        (kolmogorovExtensionFiniteWindowEventAtDefault 0 ef))
      (kolmogorovExtensionFiniteWindowDecodeBHist
        (kolmogorovExtensionFiniteWindowEventAtDefault 1 ef))
      (kolmogorovExtensionFiniteWindowDecodeBHist
        (kolmogorovExtensionFiniteWindowEventAtDefault 2 ef))
      (kolmogorovExtensionFiniteWindowDecodeBHist
        (kolmogorovExtensionFiniteWindowEventAtDefault 3 ef))
      (kolmogorovExtensionFiniteWindowDecodeBHist
        (kolmogorovExtensionFiniteWindowEventAtDefault 4 ef))
      (kolmogorovExtensionFiniteWindowDecodeBHist
        (kolmogorovExtensionFiniteWindowEventAtDefault 5 ef))
      (kolmogorovExtensionFiniteWindowDecodeBHist
        (kolmogorovExtensionFiniteWindowEventAtDefault 6 ef))
      (kolmogorovExtensionFiniteWindowDecodeBHist
        (kolmogorovExtensionFiniteWindowEventAtDefault 7 ef))
      (kolmogorovExtensionFiniteWindowDecodeBHist
        (kolmogorovExtensionFiniteWindowEventAtDefault 8 ef)))

private theorem kolmogorovExtensionFiniteWindow_round_trip :
    ∀ x : KolmogorovExtensionFiniteWindowUp,
      kolmogorovExtensionFiniteWindowFromEventFlow
          (kolmogorovExtensionFiniteWindowToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I W mu pi R H C P N =>
      change
        some
          (KolmogorovExtensionFiniteWindowUp.mk
            (kolmogorovExtensionFiniteWindowDecodeBHist
              (kolmogorovExtensionFiniteWindowEncodeBHist I))
            (kolmogorovExtensionFiniteWindowDecodeBHist
              (kolmogorovExtensionFiniteWindowEncodeBHist W))
            (kolmogorovExtensionFiniteWindowDecodeBHist
              (kolmogorovExtensionFiniteWindowEncodeBHist mu))
            (kolmogorovExtensionFiniteWindowDecodeBHist
              (kolmogorovExtensionFiniteWindowEncodeBHist pi))
            (kolmogorovExtensionFiniteWindowDecodeBHist
              (kolmogorovExtensionFiniteWindowEncodeBHist R))
            (kolmogorovExtensionFiniteWindowDecodeBHist
              (kolmogorovExtensionFiniteWindowEncodeBHist H))
            (kolmogorovExtensionFiniteWindowDecodeBHist
              (kolmogorovExtensionFiniteWindowEncodeBHist C))
            (kolmogorovExtensionFiniteWindowDecodeBHist
              (kolmogorovExtensionFiniteWindowEncodeBHist P))
            (kolmogorovExtensionFiniteWindowDecodeBHist
              (kolmogorovExtensionFiniteWindowEncodeBHist N))) =
          some (KolmogorovExtensionFiniteWindowUp.mk I W mu pi R H C P N)
      rw [kolmogorovExtensionFiniteWindowDecode_encode I,
        kolmogorovExtensionFiniteWindowDecode_encode W,
        kolmogorovExtensionFiniteWindowDecode_encode mu,
        kolmogorovExtensionFiniteWindowDecode_encode pi,
        kolmogorovExtensionFiniteWindowDecode_encode R,
        kolmogorovExtensionFiniteWindowDecode_encode H,
        kolmogorovExtensionFiniteWindowDecode_encode C,
        kolmogorovExtensionFiniteWindowDecode_encode P,
        kolmogorovExtensionFiniteWindowDecode_encode N]

private theorem kolmogorovExtensionFiniteWindowToEventFlow_injective
    {x y : KolmogorovExtensionFiniteWindowUp} :
    kolmogorovExtensionFiniteWindowToEventFlow x =
      kolmogorovExtensionFiniteWindowToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kolmogorovExtensionFiniteWindowFromEventFlow
          (kolmogorovExtensionFiniteWindowToEventFlow x) =
        kolmogorovExtensionFiniteWindowFromEventFlow
          (kolmogorovExtensionFiniteWindowToEventFlow y) :=
    congrArg kolmogorovExtensionFiniteWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kolmogorovExtensionFiniteWindow_round_trip x).symm
      (Eq.trans hread (kolmogorovExtensionFiniteWindow_round_trip y)))

instance kolmogorovExtensionFiniteWindowBHistCarrier :
    BHistCarrier KolmogorovExtensionFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kolmogorovExtensionFiniteWindowToEventFlow
  fromEventFlow := kolmogorovExtensionFiniteWindowFromEventFlow

instance kolmogorovExtensionFiniteWindowChapterTasteGate :
    ChapterTasteGate KolmogorovExtensionFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kolmogorovExtensionFiniteWindowFromEventFlow
          (kolmogorovExtensionFiniteWindowToEventFlow x) =
        some x
    exact kolmogorovExtensionFiniteWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kolmogorovExtensionFiniteWindowToEventFlow_injective heq)

def taste_gate : ChapterTasteGate KolmogorovExtensionFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kolmogorovExtensionFiniteWindowChapterTasteGate

theorem KolmogorovExtensionFiniteWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kolmogorovExtensionFiniteWindowDecodeBHist
          (kolmogorovExtensionFiniteWindowEncodeBHist h) =
        h) ∧
      (∀ x : KolmogorovExtensionFiniteWindowUp,
        kolmogorovExtensionFiniteWindowFromEventFlow
            (kolmogorovExtensionFiniteWindowToEventFlow x) =
          some x) ∧
        Nonempty (ChapterTasteGate KolmogorovExtensionFiniteWindowUp) ∧
          kolmogorovExtensionFiniteWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨kolmogorovExtensionFiniteWindowDecode_encode,
      kolmogorovExtensionFiniteWindow_round_trip,
      ⟨kolmogorovExtensionFiniteWindowChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.KolmogorovExtensionFiniteWindowUp
