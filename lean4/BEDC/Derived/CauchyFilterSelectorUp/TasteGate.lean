import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterSelectorUp : Type where
  | mk (F W R D E H C P N : BHist) : CauchyFilterSelectorUp
  deriving DecidableEq

def cauchyFilterSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterSelectorEncodeBHist h

def cauchyFilterSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterSelectorDecodeBHist tail)

private theorem cauchyFilterSelectorDecodeEncode :
    ∀ h : BHist, cauchyFilterSelectorDecodeBHist
      (cauchyFilterSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterSelectorFields : CauchyFilterSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterSelectorUp.mk F W R D E H C P N => [F, W, R, D, E, H, C, P, N]

def cauchyFilterSelectorToEventFlow : CauchyFilterSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyFilterSelectorFields x).map cauchyFilterSelectorEncodeBHist

private def cauchyFilterSelectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterSelectorEventAtDefault index rest

def cauchyFilterSelectorFromEventFlow : EventFlow → Option CauchyFilterSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyFilterSelectorUp.mk
        (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEventAtDefault 0 ef))
        (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEventAtDefault 1 ef))
        (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEventAtDefault 2 ef))
        (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEventAtDefault 3 ef))
        (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEventAtDefault 4 ef))
        (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEventAtDefault 5 ef))
        (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEventAtDefault 6 ef))
        (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEventAtDefault 7 ef))
        (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEventAtDefault 8 ef)))

private theorem cauchyFilterSelectorRoundTrip :
    ∀ x : CauchyFilterSelectorUp,
      cauchyFilterSelectorFromEventFlow (cauchyFilterSelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F W R D E H C P N =>
      change
        some
          (CauchyFilterSelectorUp.mk
            (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEncodeBHist F))
            (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEncodeBHist W))
            (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEncodeBHist R))
            (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEncodeBHist D))
            (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEncodeBHist E))
            (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEncodeBHist H))
            (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEncodeBHist C))
            (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEncodeBHist P))
            (cauchyFilterSelectorDecodeBHist (cauchyFilterSelectorEncodeBHist N))) =
          some (CauchyFilterSelectorUp.mk F W R D E H C P N)
      rw [cauchyFilterSelectorDecodeEncode F, cauchyFilterSelectorDecodeEncode W,
        cauchyFilterSelectorDecodeEncode R, cauchyFilterSelectorDecodeEncode D,
        cauchyFilterSelectorDecodeEncode E, cauchyFilterSelectorDecodeEncode H,
        cauchyFilterSelectorDecodeEncode C, cauchyFilterSelectorDecodeEncode P,
        cauchyFilterSelectorDecodeEncode N]

private theorem cauchyFilterSelectorToEventFlow_injective
    {x y : CauchyFilterSelectorUp} :
    cauchyFilterSelectorToEventFlow x = cauchyFilterSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterSelectorFromEventFlow (cauchyFilterSelectorToEventFlow x) =
        cauchyFilterSelectorFromEventFlow (cauchyFilterSelectorToEventFlow y) :=
    congrArg cauchyFilterSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyFilterSelectorRoundTrip x).symm
      (Eq.trans hread (cauchyFilterSelectorRoundTrip y)))

instance cauchyFilterSelectorBHistCarrier : BHistCarrier CauchyFilterSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterSelectorToEventFlow
  fromEventFlow := cauchyFilterSelectorFromEventFlow

instance cauchyFilterSelectorChapterTasteGate : ChapterTasteGate CauchyFilterSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterSelectorFromEventFlow (cauchyFilterSelectorToEventFlow x) = some x
    exact cauchyFilterSelectorRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyFilterSelectorToEventFlow_injective heq)

theorem CauchyFilterSelectorTasteGate_single_carrier_alignment :
    cauchyFilterSelectorEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist, cauchyFilterSelectorDecodeBHist
        (cauchyFilterSelectorEncodeBHist h) = h) ∧
        (∀ x : CauchyFilterSelectorUp,
          cauchyFilterSelectorFromEventFlow (cauchyFilterSelectorToEventFlow x) = some x) ∧
          Nonempty (BHistCarrier CauchyFilterSelectorUp) ∧
            Nonempty (ChapterTasteGate CauchyFilterSelectorUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, cauchyFilterSelectorDecodeEncode, cauchyFilterSelectorRoundTrip,
      ⟨cauchyFilterSelectorBHistCarrier⟩, ⟨cauchyFilterSelectorChapterTasteGate⟩⟩

end BEDC.Derived.CauchyFilterSelectorUp
