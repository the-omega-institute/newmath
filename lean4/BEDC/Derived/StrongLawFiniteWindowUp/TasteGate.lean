import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StrongLawFiniteWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StrongLawFiniteWindowUp : Type where
  | mk (P R W C B E H T Q N : BHist) : StrongLawFiniteWindowUp
  deriving DecidableEq

def strongLawFiniteWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: strongLawFiniteWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: strongLawFiniteWindowEncodeBHist h

def strongLawFiniteWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (strongLawFiniteWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (strongLawFiniteWindowDecodeBHist tail)

private theorem StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def strongLawFiniteWindowFields : StrongLawFiniteWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StrongLawFiniteWindowUp.mk P R W C B E H T Q N => [P, R, W, C, B, E, H, T, Q, N]

def strongLawFiniteWindowToEventFlow : StrongLawFiniteWindowUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (strongLawFiniteWindowFields x).map strongLawFiniteWindowEncodeBHist

private def strongLawFiniteWindowEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => strongLawFiniteWindowEventAtDefault index rest

def strongLawFiniteWindowFromEventFlow (ef : EventFlow) : Option StrongLawFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StrongLawFiniteWindowUp.mk
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 0 ef))
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 1 ef))
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 2 ef))
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 3 ef))
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 4 ef))
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 5 ef))
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 6 ef))
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 7 ef))
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 8 ef))
      (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEventAtDefault 9 ef)))

private theorem StrongLawFiniteWindowTasteGate_single_carrier_alignment_round_trip
    (x : StrongLawFiniteWindowUp) :
    strongLawFiniteWindowFromEventFlow (strongLawFiniteWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P R W C B E H T Q N =>
      change
        some
          (StrongLawFiniteWindowUp.mk
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist P))
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist R))
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist W))
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist C))
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist B))
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist E))
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist H))
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist T))
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist Q))
            (strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist N))) =
          some (StrongLawFiniteWindowUp.mk P R W C B E H T Q N)
      rw [StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode P,
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode R,
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode W,
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode C,
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode B,
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode E,
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode H,
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode T,
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode Q,
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode N]

private theorem StrongLawFiniteWindowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StrongLawFiniteWindowUp} :
    strongLawFiniteWindowToEventFlow x = strongLawFiniteWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      strongLawFiniteWindowFromEventFlow (strongLawFiniteWindowToEventFlow x) =
        strongLawFiniteWindowFromEventFlow (strongLawFiniteWindowToEventFlow y) :=
    congrArg strongLawFiniteWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StrongLawFiniteWindowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StrongLawFiniteWindowTasteGate_single_carrier_alignment_round_trip y)))

instance strongLawFiniteWindowBHistCarrier : BHistCarrier StrongLawFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := strongLawFiniteWindowToEventFlow
  fromEventFlow := strongLawFiniteWindowFromEventFlow

instance strongLawFiniteWindowChapterTasteGate :
    ChapterTasteGate StrongLawFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change strongLawFiniteWindowFromEventFlow (strongLawFiniteWindowToEventFlow x) = some x
    exact StrongLawFiniteWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StrongLawFiniteWindowTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def strongLawFiniteWindowTasteGate : ChapterTasteGate StrongLawFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  strongLawFiniteWindowChapterTasteGate

theorem StrongLawFiniteWindowTasteGate_single_carrier_alignment :
    strongLawFiniteWindowEncodeBHist BHist.Empty = [] ∧
      strongLawFiniteWindowEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        strongLawFiniteWindowEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] ∧
          (∀ h : BHist,
            strongLawFiniteWindowDecodeBHist (strongLawFiniteWindowEncodeBHist h) = h) ∧
            (∀ x : StrongLawFiniteWindowUp,
              strongLawFiniteWindowFromEventFlow (strongLawFiniteWindowToEventFlow x) = some x) ∧
              Function.Injective strongLawFiniteWindowToEventFlow := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, rfl, rfl, StrongLawFiniteWindowTasteGate_single_carrier_alignment_decode,
      StrongLawFiniteWindowTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        StrongLawFiniteWindowTasteGate_single_carrier_alignment_toEventFlow_injective heq⟩

end BEDC.Derived.StrongLawFiniteWindowUp
