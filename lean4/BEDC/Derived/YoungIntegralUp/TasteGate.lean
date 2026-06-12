import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.YoungIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive YoungIntegralUp : Type where
  | mk (F G V C S D R E H K P N : BHist) : YoungIntegralUp
  deriving DecidableEq

def youngIntegralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: youngIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: youngIntegralEncodeBHist h

def youngIntegralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (youngIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (youngIntegralDecodeBHist tail)

private theorem YoungIntegralTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, youngIntegralDecodeBHist (youngIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def youngIntegralFields : YoungIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | YoungIntegralUp.mk F G V C S D R E H K P N => [F, G, V, C, S, D, R, E, H, K, P, N]

def youngIntegralToEventFlow : YoungIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (youngIntegralFields x).map youngIntegralEncodeBHist

private def youngIntegralEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => youngIntegralEventAtDefault index rest

def youngIntegralFromEventFlow : EventFlow → Option YoungIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (YoungIntegralUp.mk
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 0 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 1 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 2 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 3 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 4 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 5 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 6 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 7 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 8 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 9 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 10 ef))
        (youngIntegralDecodeBHist (youngIntegralEventAtDefault 11 ef)))

private theorem YoungIntegralTasteGate_single_carrier_alignment_round_trip :
    ∀ x : YoungIntegralUp,
      youngIntegralFromEventFlow (youngIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G V C S D R E H K P N =>
      change
        some
          (YoungIntegralUp.mk
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist F))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist G))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist V))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist C))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist S))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist D))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist R))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist E))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist H))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist K))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist P))
            (youngIntegralDecodeBHist (youngIntegralEncodeBHist N))) =
          some (YoungIntegralUp.mk F G V C S D R E H K P N)
      rw [YoungIntegralTasteGate_single_carrier_alignment_decode F,
        YoungIntegralTasteGate_single_carrier_alignment_decode G,
        YoungIntegralTasteGate_single_carrier_alignment_decode V,
        YoungIntegralTasteGate_single_carrier_alignment_decode C,
        YoungIntegralTasteGate_single_carrier_alignment_decode S,
        YoungIntegralTasteGate_single_carrier_alignment_decode D,
        YoungIntegralTasteGate_single_carrier_alignment_decode R,
        YoungIntegralTasteGate_single_carrier_alignment_decode E,
        YoungIntegralTasteGate_single_carrier_alignment_decode H,
        YoungIntegralTasteGate_single_carrier_alignment_decode K,
        YoungIntegralTasteGate_single_carrier_alignment_decode P,
        YoungIntegralTasteGate_single_carrier_alignment_decode N]

theorem youngIntegralToEventFlow_injective {x y : YoungIntegralUp} :
    youngIntegralToEventFlow x = youngIntegralToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      youngIntegralFromEventFlow (youngIntegralToEventFlow x) =
        youngIntegralFromEventFlow (youngIntegralToEventFlow y) :=
    congrArg youngIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (YoungIntegralTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (YoungIntegralTasteGate_single_carrier_alignment_round_trip y)))

instance youngIntegralBHistCarrier : BHistCarrier YoungIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := youngIntegralToEventFlow
  fromEventFlow := youngIntegralFromEventFlow

instance youngIntegralChapterTasteGate : ChapterTasteGate YoungIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change youngIntegralFromEventFlow (youngIntegralToEventFlow x) = some x
    exact YoungIntegralTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (youngIntegralToEventFlow_injective heq)

def taste_gate : ChapterTasteGate YoungIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  youngIntegralChapterTasteGate

theorem YoungIntegralTasteGate_single_carrier_alignment :
    (∀ h : BHist, youngIntegralDecodeBHist (youngIntegralEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier YoungIntegralUp) ∧
        Nonempty (ChapterTasteGate YoungIntegralUp) ∧
          youngIntegralEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact YoungIntegralTasteGate_single_carrier_alignment_decode
  constructor
  · exact ⟨youngIntegralBHistCarrier⟩
  constructor
  · exact ⟨youngIntegralChapterTasteGate⟩
  · rfl

end BEDC.Derived.YoungIntegralUp
