import BEDC.Derived.RiemannIntegralUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def riemannIntegralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannIntegralEncodeBHist h

def riemannIntegralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannIntegralDecodeBHist tail)

private theorem RiemannIntegralTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      riemannIntegralDecodeBHist (riemannIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def riemannIntegralToEventFlow : RiemannIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannIntegralUp.mk M T F S D G R H C P N =>
      [riemannIntegralEncodeBHist M,
        riemannIntegralEncodeBHist T,
        riemannIntegralEncodeBHist F,
        riemannIntegralEncodeBHist S,
        riemannIntegralEncodeBHist D,
        riemannIntegralEncodeBHist G,
        riemannIntegralEncodeBHist R,
        riemannIntegralEncodeBHist H,
        riemannIntegralEncodeBHist C,
        riemannIntegralEncodeBHist P,
        riemannIntegralEncodeBHist N]

private def riemannIntegralEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannIntegralEventAtDefault index rest

def riemannIntegralFromEventFlow (ef : EventFlow) : Option RiemannIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannIntegralUp.mk
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 0 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 1 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 2 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 3 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 4 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 5 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 6 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 7 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 8 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 9 ef))
      (riemannIntegralDecodeBHist (riemannIntegralEventAtDefault 10 ef)))

private theorem RiemannIntegralTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RiemannIntegralUp,
      riemannIntegralFromEventFlow (riemannIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M T F S D G R H C P N =>
      change
        some
          (RiemannIntegralUp.mk
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist M))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist T))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist F))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist S))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist D))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist G))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist R))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist H))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist C))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist P))
            (riemannIntegralDecodeBHist (riemannIntegralEncodeBHist N))) =
          some (RiemannIntegralUp.mk M T F S D G R H C P N)
      rw [RiemannIntegralTasteGate_single_carrier_alignment_decode M,
        RiemannIntegralTasteGate_single_carrier_alignment_decode T,
        RiemannIntegralTasteGate_single_carrier_alignment_decode F,
        RiemannIntegralTasteGate_single_carrier_alignment_decode S,
        RiemannIntegralTasteGate_single_carrier_alignment_decode D,
        RiemannIntegralTasteGate_single_carrier_alignment_decode G,
        RiemannIntegralTasteGate_single_carrier_alignment_decode R,
        RiemannIntegralTasteGate_single_carrier_alignment_decode H,
        RiemannIntegralTasteGate_single_carrier_alignment_decode C,
        RiemannIntegralTasteGate_single_carrier_alignment_decode P,
        RiemannIntegralTasteGate_single_carrier_alignment_decode N]

private theorem riemannIntegralToEventFlow_injective {x y : RiemannIntegralUp} :
    riemannIntegralToEventFlow x = riemannIntegralToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannIntegralFromEventFlow (riemannIntegralToEventFlow x) =
        riemannIntegralFromEventFlow (riemannIntegralToEventFlow y) :=
    congrArg riemannIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RiemannIntegralTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RiemannIntegralTasteGate_single_carrier_alignment_round_trip y)))

instance riemannIntegralBHistCarrier : BHistCarrier RiemannIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannIntegralToEventFlow
  fromEventFlow := riemannIntegralFromEventFlow

instance riemannIntegralChapterTasteGate : ChapterTasteGate RiemannIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := RiemannIntegralTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (riemannIntegralToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RiemannIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  riemannIntegralChapterTasteGate

theorem RiemannIntegralTasteGate_single_carrier_alignment :
    (∀ h : BHist, riemannIntegralDecodeBHist (riemannIntegralEncodeBHist h) = h) ∧
      (∀ x : RiemannIntegralUp,
        riemannIntegralFromEventFlow (riemannIntegralToEventFlow x) = some x) ∧
        (∀ x y : RiemannIntegralUp,
          riemannIntegralToEventFlow x = riemannIntegralToEventFlow y → x = y) ∧
          riemannIntegralEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RiemannIntegralTasteGate_single_carrier_alignment_decode,
      RiemannIntegralTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => riemannIntegralToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RiemannIntegralUp
