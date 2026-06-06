import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocalizedCauchyRateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocalizedCauchyRateUp : Type where
  | mk (W D T R S Q E H C P N : BHist) : LocalizedCauchyRateUp
  deriving DecidableEq

def localizedCauchyRateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: localizedCauchyRateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: localizedCauchyRateEncodeBHist h

def localizedCauchyRateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (localizedCauchyRateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (localizedCauchyRateDecodeBHist tail)

private theorem LocalizedCauchyRateTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def localizedCauchyRateFields : LocalizedCauchyRateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocalizedCauchyRateUp.mk W D T R S Q E H C P N => [W, D, T, R, S, Q, E, H, C, P, N]

def localizedCauchyRateToEventFlow : LocalizedCauchyRateUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (localizedCauchyRateFields x).map localizedCauchyRateEncodeBHist

private def localizedCauchyRateEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => localizedCauchyRateEventAtDefault index rest

def localizedCauchyRateFromEventFlow (ef : EventFlow) : Option LocalizedCauchyRateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocalizedCauchyRateUp.mk
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 0 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 1 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 2 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 3 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 4 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 5 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 6 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 7 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 8 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 9 ef))
      (localizedCauchyRateDecodeBHist (localizedCauchyRateEventAtDefault 10 ef)))

private theorem localizedCauchyRate_round_trip :
    ∀ x : LocalizedCauchyRateUp,
      localizedCauchyRateFromEventFlow (localizedCauchyRateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W D T R S Q E H C P N =>
      change
        some
            (LocalizedCauchyRateUp.mk
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist W))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist D))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist T))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist R))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist S))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist Q))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist E))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist H))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist C))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist P))
              (localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist N))) =
          some (LocalizedCauchyRateUp.mk W D T R S Q E H C P N)
      rw [LocalizedCauchyRateTasteGate_single_carrier_alignment_decode W,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode D,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode T,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode R,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode S,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode Q,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode E,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode H,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode C,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode P,
        LocalizedCauchyRateTasteGate_single_carrier_alignment_decode N]

private theorem localizedCauchyRateToEventFlow_injective
    {x y : LocalizedCauchyRateUp} :
    localizedCauchyRateToEventFlow x = localizedCauchyRateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localizedCauchyRateFromEventFlow (localizedCauchyRateToEventFlow x) =
        localizedCauchyRateFromEventFlow (localizedCauchyRateToEventFlow y) :=
    congrArg localizedCauchyRateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (localizedCauchyRate_round_trip x).symm
      (Eq.trans hread (localizedCauchyRate_round_trip y)))

instance localizedCauchyRateBHistCarrier : BHistCarrier LocalizedCauchyRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := localizedCauchyRateToEventFlow
  fromEventFlow := localizedCauchyRateFromEventFlow

instance localizedCauchyRateChapterTasteGate :
    ChapterTasteGate LocalizedCauchyRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change localizedCauchyRateFromEventFlow (localizedCauchyRateToEventFlow x) = some x
    exact localizedCauchyRate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (localizedCauchyRateToEventFlow_injective heq)

theorem LocalizedCauchyRateTasteGate_single_carrier_alignment :
    (∀ h : BHist, localizedCauchyRateDecodeBHist (localizedCauchyRateEncodeBHist h) = h) ∧
      (∀ x : LocalizedCauchyRateUp,
        localizedCauchyRateFromEventFlow (localizedCauchyRateToEventFlow x) = some x) ∧
        (∀ x y : LocalizedCauchyRateUp,
          localizedCauchyRateToEventFlow x = localizedCauchyRateToEventFlow y → x = y) ∧
          localizedCauchyRateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact LocalizedCauchyRateTasteGate_single_carrier_alignment_decode
  · constructor
    · exact localizedCauchyRate_round_trip
    · constructor
      · intro x y heq
        exact localizedCauchyRateToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocalizedCauchyRateUp
