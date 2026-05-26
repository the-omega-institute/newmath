import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealConvergenceRateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealConvergenceRateUp : Type where
  | mk (R S D Q E H C P N : BHist) : RealConvergenceRateUp
  deriving DecidableEq

def realConvergenceRateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realConvergenceRateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realConvergenceRateEncodeBHist h

def realConvergenceRateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realConvergenceRateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realConvergenceRateDecodeBHist tail)

private theorem RealConvergenceRateTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realConvergenceRateFields : RealConvergenceRateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealConvergenceRateUp.mk R S D Q E H C P N => [R, S, D, Q, E, H, C, P, N]

def realConvergenceRateToEventFlow : RealConvergenceRateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realConvergenceRateFields x).map realConvergenceRateEncodeBHist

private def realConvergenceRateEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realConvergenceRateEventAt index rest

def realConvergenceRateFromEventFlow : EventFlow → Option RealConvergenceRateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (RealConvergenceRateUp.mk
          (realConvergenceRateDecodeBHist (realConvergenceRateEventAt 0 flow))
          (realConvergenceRateDecodeBHist (realConvergenceRateEventAt 1 flow))
          (realConvergenceRateDecodeBHist (realConvergenceRateEventAt 2 flow))
          (realConvergenceRateDecodeBHist (realConvergenceRateEventAt 3 flow))
          (realConvergenceRateDecodeBHist (realConvergenceRateEventAt 4 flow))
          (realConvergenceRateDecodeBHist (realConvergenceRateEventAt 5 flow))
          (realConvergenceRateDecodeBHist (realConvergenceRateEventAt 6 flow))
          (realConvergenceRateDecodeBHist (realConvergenceRateEventAt 7 flow))
          (realConvergenceRateDecodeBHist (realConvergenceRateEventAt 8 flow)))

private theorem RealConvergenceRateTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealConvergenceRateUp,
      realConvergenceRateFromEventFlow (realConvergenceRateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S D Q E H C P N =>
      change
        some
          (RealConvergenceRateUp.mk
            (realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist R))
            (realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist S))
            (realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist D))
            (realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist Q))
            (realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist E))
            (realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist H))
            (realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist C))
            (realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist P))
            (realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist N))) =
          some (RealConvergenceRateUp.mk R S D Q E H C P N)
      rw [RealConvergenceRateTasteGate_single_carrier_alignment_decode R,
        RealConvergenceRateTasteGate_single_carrier_alignment_decode S,
        RealConvergenceRateTasteGate_single_carrier_alignment_decode D,
        RealConvergenceRateTasteGate_single_carrier_alignment_decode Q,
        RealConvergenceRateTasteGate_single_carrier_alignment_decode E,
        RealConvergenceRateTasteGate_single_carrier_alignment_decode H,
        RealConvergenceRateTasteGate_single_carrier_alignment_decode C,
        RealConvergenceRateTasteGate_single_carrier_alignment_decode P,
        RealConvergenceRateTasteGate_single_carrier_alignment_decode N]

private theorem RealConvergenceRateTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealConvergenceRateUp} :
    realConvergenceRateToEventFlow x = realConvergenceRateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realConvergenceRateFromEventFlow (realConvergenceRateToEventFlow x) =
        realConvergenceRateFromEventFlow (realConvergenceRateToEventFlow y) :=
    congrArg realConvergenceRateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealConvergenceRateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealConvergenceRateTasteGate_single_carrier_alignment_round_trip y)))

instance realConvergenceRateBHistCarrier : BHistCarrier RealConvergenceRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realConvergenceRateToEventFlow
  fromEventFlow := realConvergenceRateFromEventFlow

instance realConvergenceRateChapterTasteGate : ChapterTasteGate RealConvergenceRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realConvergenceRateFromEventFlow (realConvergenceRateToEventFlow x) = some x
    exact RealConvergenceRateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealConvergenceRateTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RealConvergenceRateTasteGate_single_carrier_alignment :
    (∀ h : BHist, realConvergenceRateDecodeBHist (realConvergenceRateEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealConvergenceRateUp) ∧
        Nonempty (ChapterTasteGate RealConvergenceRateUp) ∧
          realConvergenceRateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealConvergenceRateTasteGate_single_carrier_alignment_decode,
      ⟨realConvergenceRateBHistCarrier⟩,
      ⟨realConvergenceRateChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealConvergenceRateUp
