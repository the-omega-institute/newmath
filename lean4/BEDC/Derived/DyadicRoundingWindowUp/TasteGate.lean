import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicRoundingWindowUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicRoundingWindowUp : Type where
  | mk (S q D A R E H C P N : BHist) : DyadicRoundingWindowUp
  deriving DecidableEq

def dyadicRoundingWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicRoundingWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicRoundingWindowEncodeBHist h

def dyadicRoundingWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicRoundingWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicRoundingWindowDecodeBHist tail)

private theorem dyadicRoundingWindow_decode_encode :
    ∀ h : BHist,
      dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicRoundingWindowToEventFlow : DyadicRoundingWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicRoundingWindowUp.mk S q D A R E H C P N =>
      [dyadicRoundingWindowEncodeBHist S, dyadicRoundingWindowEncodeBHist q,
        dyadicRoundingWindowEncodeBHist D, dyadicRoundingWindowEncodeBHist A,
        dyadicRoundingWindowEncodeBHist R, dyadicRoundingWindowEncodeBHist E,
        dyadicRoundingWindowEncodeBHist H, dyadicRoundingWindowEncodeBHist C,
        dyadicRoundingWindowEncodeBHist P, dyadicRoundingWindowEncodeBHist N]

private def dyadicRoundingWindowEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicRoundingWindowEventAt index rest

def dyadicRoundingWindowFromEventFlow : EventFlow → Option DyadicRoundingWindowUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (DyadicRoundingWindowUp.mk
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 0 flow))
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 1 flow))
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 2 flow))
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 3 flow))
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 4 flow))
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 5 flow))
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 6 flow))
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 7 flow))
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 8 flow))
          (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEventAt 9 flow)))

private theorem dyadicRoundingWindow_round_trip :
    ∀ x : DyadicRoundingWindowUp,
      dyadicRoundingWindowFromEventFlow (dyadicRoundingWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S q D A R E H C P N =>
      change
        some
          (DyadicRoundingWindowUp.mk
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist S))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist q))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist D))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist A))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist R))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist E))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist H))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist C))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist P))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist N))) =
          some (DyadicRoundingWindowUp.mk S q D A R E H C P N)
      rw [dyadicRoundingWindow_decode_encode S, dyadicRoundingWindow_decode_encode q,
        dyadicRoundingWindow_decode_encode D, dyadicRoundingWindow_decode_encode A,
        dyadicRoundingWindow_decode_encode R, dyadicRoundingWindow_decode_encode E,
        dyadicRoundingWindow_decode_encode H, dyadicRoundingWindow_decode_encode C,
        dyadicRoundingWindow_decode_encode P, dyadicRoundingWindow_decode_encode N]

private theorem dyadicRoundingWindowToEventFlow_injective {x y : DyadicRoundingWindowUp} :
    dyadicRoundingWindowToEventFlow x = dyadicRoundingWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicRoundingWindowFromEventFlow (dyadicRoundingWindowToEventFlow x) =
        dyadicRoundingWindowFromEventFlow (dyadicRoundingWindowToEventFlow y) :=
    congrArg dyadicRoundingWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicRoundingWindow_round_trip x).symm
      (Eq.trans hread (dyadicRoundingWindow_round_trip y)))

instance dyadicRoundingWindowBHistCarrier : BHistCarrier DyadicRoundingWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicRoundingWindowToEventFlow
  fromEventFlow := dyadicRoundingWindowFromEventFlow

instance dyadicRoundingWindowChapterTasteGate :
    ChapterTasteGate DyadicRoundingWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicRoundingWindowFromEventFlow (dyadicRoundingWindowToEventFlow x) = some x
    exact dyadicRoundingWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicRoundingWindowToEventFlow_injective heq)

theorem DyadicRoundingWindowTasteGate_single_carrier_alignment :
    (forall h : BHist,
      dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist h) = h) /\
      Nonempty (ChapterTasteGate DyadicRoundingWindowUp) /\
        (forall x : DyadicRoundingWindowUp,
          exists e : EventFlow, BHistCarrier.fromEventFlow e = some x) /\
          dyadicRoundingWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨dyadicRoundingWindow_decode_encode,
      ⟨⟨dyadicRoundingWindowChapterTasteGate⟩,
        ⟨fun x =>
          ⟨dyadicRoundingWindowToEventFlow x,
            by
              change
                dyadicRoundingWindowFromEventFlow (dyadicRoundingWindowToEventFlow x) =
                  some x
              exact dyadicRoundingWindow_round_trip x⟩,
          rfl⟩⟩⟩

end BEDC.Derived.DyadicRoundingWindowUp.TasteGate
