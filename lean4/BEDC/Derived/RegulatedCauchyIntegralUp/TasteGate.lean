import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedCauchyIntegralUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedCauchyIntegralUp : Type where
  | mk (G T A W R E H C P N : BHist) : RegulatedCauchyIntegralUp
  deriving DecidableEq

def regulatedCauchyIntegralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedCauchyIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedCauchyIntegralEncodeBHist h

def regulatedCauchyIntegralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedCauchyIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedCauchyIntegralDecodeBHist tail)

private theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedCauchyIntegralFields : RegulatedCauchyIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedCauchyIntegralUp.mk G T A W R E H C P N => [G, T, A, W, R, E, H, C, P, N]

def regulatedCauchyIntegralToEventFlow : RegulatedCauchyIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regulatedCauchyIntegralFields x).map regulatedCauchyIntegralEncodeBHist

private def RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt index rest

def regulatedCauchyIntegralFromEventFlow : EventFlow → Option RegulatedCauchyIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegulatedCauchyIntegralUp.mk
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 0 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 1 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 2 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 3 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 4 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 5 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 6 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 7 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 8 ef))
        (regulatedCauchyIntegralDecodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegulatedCauchyIntegralUp,
      regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G T A W R E H C P N =>
      change
        some
          (RegulatedCauchyIntegralUp.mk
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist G))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist T))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist A))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist W))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist R))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist E))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist H))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist C))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist P))
            (regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist N))) =
          some (RegulatedCauchyIntegralUp.mk G T A W R E H C P N)
      rw [RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode G,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode T,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode A,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode W,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode R,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode E,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode H,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode C,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode P,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode N]

private theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatedCauchyIntegralUp} :
    regulatedCauchyIntegralToEventFlow x = regulatedCauchyIntegralToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow x) =
        regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow y) :=
    congrArg regulatedCauchyIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedCauchyIntegralBHistCarrier : BHistCarrier RegulatedCauchyIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedCauchyIntegralToEventFlow
  fromEventFlow := regulatedCauchyIntegralFromEventFlow

instance regulatedCauchyIntegralChapterTasteGate :
    ChapterTasteGate RegulatedCauchyIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow x) = some x
    exact RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regulatedCauchyIntegralDecodeBHist (regulatedCauchyIntegralEncodeBHist h) = h) ∧
      (∀ x : RegulatedCauchyIntegralUp,
        regulatedCauchyIntegralFromEventFlow (regulatedCauchyIntegralToEventFlow x) = some x) ∧
        (∀ x y : RegulatedCauchyIntegralUp,
          regulatedCauchyIntegralToEventFlow x = regulatedCauchyIntegralToEventFlow y →
            x = y) ∧
          regulatedCauchyIntegralEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode,
      RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegulatedCauchyIntegralUp.TasteGate
