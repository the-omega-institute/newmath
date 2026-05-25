import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EngelExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EngelExpansionUp : Type where
  | mk
      (denominatorSchedule partialSums remainderBounds streamWindows regularReadback
        realSeal transportRows replayRows provenance nameCert : BHist) :
      EngelExpansionUp
  deriving DecidableEq

def engelExpansionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: engelExpansionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: engelExpansionEncodeBHist h

def engelExpansionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (engelExpansionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (engelExpansionDecodeBHist tail)

private theorem EngelExpansionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, engelExpansionDecodeBHist (engelExpansionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def engelExpansionFields : EngelExpansionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EngelExpansionUp.mk denominatorSchedule partialSums remainderBounds streamWindows
      regularReadback realSeal transportRows replayRows provenance nameCert =>
      [denominatorSchedule, partialSums, remainderBounds, streamWindows, regularReadback,
        realSeal, transportRows, replayRows, provenance, nameCert]

def engelExpansionToEventFlow : EngelExpansionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (engelExpansionFields x).map engelExpansionEncodeBHist

private def engelExpansionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => engelExpansionEventAtDefault index rest

def engelExpansionFromEventFlow : EventFlow → Option EngelExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (EngelExpansionUp.mk
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 0 ef))
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 1 ef))
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 2 ef))
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 3 ef))
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 4 ef))
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 5 ef))
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 6 ef))
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 7 ef))
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 8 ef))
        (engelExpansionDecodeBHist (engelExpansionEventAtDefault 9 ef)))

private theorem EngelExpansionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EngelExpansionUp,
      engelExpansionFromEventFlow (engelExpansionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk denominatorSchedule partialSums remainderBounds streamWindows regularReadback
      realSeal transportRows replayRows provenance nameCert =>
      change
        some
          (EngelExpansionUp.mk
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist denominatorSchedule))
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist partialSums))
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist remainderBounds))
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist streamWindows))
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist regularReadback))
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist realSeal))
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist transportRows))
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist replayRows))
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist provenance))
            (engelExpansionDecodeBHist (engelExpansionEncodeBHist nameCert))) =
          some
            (EngelExpansionUp.mk denominatorSchedule partialSums remainderBounds
              streamWindows regularReadback realSeal transportRows replayRows provenance
              nameCert)
      rw [EngelExpansionTasteGate_single_carrier_alignment_decode denominatorSchedule,
        EngelExpansionTasteGate_single_carrier_alignment_decode partialSums,
        EngelExpansionTasteGate_single_carrier_alignment_decode remainderBounds,
        EngelExpansionTasteGate_single_carrier_alignment_decode streamWindows,
        EngelExpansionTasteGate_single_carrier_alignment_decode regularReadback,
        EngelExpansionTasteGate_single_carrier_alignment_decode realSeal,
        EngelExpansionTasteGate_single_carrier_alignment_decode transportRows,
        EngelExpansionTasteGate_single_carrier_alignment_decode replayRows,
        EngelExpansionTasteGate_single_carrier_alignment_decode provenance,
        EngelExpansionTasteGate_single_carrier_alignment_decode nameCert]

private theorem engelExpansionToEventFlow_injective {x y : EngelExpansionUp} :
    engelExpansionToEventFlow x = engelExpansionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      engelExpansionFromEventFlow (engelExpansionToEventFlow x) =
        engelExpansionFromEventFlow (engelExpansionToEventFlow y) :=
    congrArg engelExpansionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EngelExpansionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EngelExpansionTasteGate_single_carrier_alignment_round_trip y)))

instance engelExpansionBHistCarrier : BHistCarrier EngelExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := engelExpansionToEventFlow
  fromEventFlow := engelExpansionFromEventFlow

instance engelExpansionChapterTasteGate : ChapterTasteGate EngelExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change engelExpansionFromEventFlow (engelExpansionToEventFlow x) = some x
    exact EngelExpansionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (engelExpansionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate EngelExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  engelExpansionChapterTasteGate

theorem EngelExpansionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier EngelExpansionUp) ∧
      Nonempty (ChapterTasteGate EngelExpansionUp) ∧
      (∀ h : BHist, engelExpansionDecodeBHist (engelExpansionEncodeBHist h) = h) ∧
      engelExpansionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨engelExpansionBHistCarrier⟩
  constructor
  · exact ⟨engelExpansionChapterTasteGate⟩
  constructor
  · exact EngelExpansionTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.EngelExpansionUp
