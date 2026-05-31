import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuousCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuousCompletionUp : Type where
  | mk
      (equicontinuityFamily uniformCompletion completeMetric cauchySequenceSpace
        streamWindows regularRationalReadback realSeal routeLedger transportRows replayRows
        provenance nameCert : BHist) :
      EquicontinuousCompletionUp
  deriving DecidableEq

def equicontinuousCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuousCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuousCompletionEncodeBHist h

def equicontinuousCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuousCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuousCompletionDecodeBHist tail)

private theorem EquicontinuousCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      equicontinuousCompletionDecodeBHist (equicontinuousCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def equicontinuousCompletionFields : EquicontinuousCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuousCompletionUp.mk equicontinuityFamily uniformCompletion completeMetric
      cauchySequenceSpace streamWindows regularRationalReadback realSeal routeLedger
      transportRows replayRows provenance nameCert =>
      [equicontinuityFamily, uniformCompletion, completeMetric, cauchySequenceSpace,
        streamWindows, regularRationalReadback, realSeal, routeLedger, transportRows,
        replayRows, provenance, nameCert]

def equicontinuousCompletionToEventFlow : EquicontinuousCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (equicontinuousCompletionFields x).map equicontinuousCompletionEncodeBHist

private def equicontinuousCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => equicontinuousCompletionEventAtDefault index rest

def equicontinuousCompletionFromEventFlow : EventFlow → Option EquicontinuousCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (EquicontinuousCompletionUp.mk
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 0 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 1 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 2 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 3 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 4 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 5 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 6 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 7 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 8 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 9 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 10 ef))
        (equicontinuousCompletionDecodeBHist (equicontinuousCompletionEventAtDefault 11 ef)))

private theorem EquicontinuousCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EquicontinuousCompletionUp,
      equicontinuousCompletionFromEventFlow (equicontinuousCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk equicontinuityFamily uniformCompletion completeMetric cauchySequenceSpace
      streamWindows regularRationalReadback realSeal routeLedger transportRows replayRows
      provenance nameCert =>
      change
        some
          (EquicontinuousCompletionUp.mk
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist equicontinuityFamily))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist uniformCompletion))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist completeMetric))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist cauchySequenceSpace))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist streamWindows))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist regularRationalReadback))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist realSeal))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist routeLedger))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist transportRows))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist replayRows))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist provenance))
            (equicontinuousCompletionDecodeBHist
              (equicontinuousCompletionEncodeBHist nameCert))) =
          some
            (EquicontinuousCompletionUp.mk equicontinuityFamily uniformCompletion
              completeMetric cauchySequenceSpace streamWindows regularRationalReadback
              realSeal routeLedger transportRows replayRows provenance nameCert)
      rw [EquicontinuousCompletionTasteGate_single_carrier_alignment_decode
          equicontinuityFamily,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode uniformCompletion,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode completeMetric,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode cauchySequenceSpace,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode streamWindows,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode
          regularRationalReadback,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode realSeal,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode routeLedger,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode transportRows,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode replayRows,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode provenance,
        EquicontinuousCompletionTasteGate_single_carrier_alignment_decode nameCert]

private theorem equicontinuousCompletionToEventFlow_injective
    {x y : EquicontinuousCompletionUp} :
    equicontinuousCompletionToEventFlow x = equicontinuousCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuousCompletionFromEventFlow (equicontinuousCompletionToEventFlow x) =
        equicontinuousCompletionFromEventFlow (equicontinuousCompletionToEventFlow y) :=
    congrArg equicontinuousCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EquicontinuousCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EquicontinuousCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance equicontinuousCompletionBHistCarrier :
    BHistCarrier EquicontinuousCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuousCompletionToEventFlow
  fromEventFlow := equicontinuousCompletionFromEventFlow

instance equicontinuousCompletionChapterTasteGate :
    ChapterTasteGate EquicontinuousCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change equicontinuousCompletionFromEventFlow (equicontinuousCompletionToEventFlow x) =
      some x
    exact EquicontinuousCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (equicontinuousCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate EquicontinuousCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  equicontinuousCompletionChapterTasteGate

theorem EquicontinuousCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier EquicontinuousCompletionUp) ∧
      Nonempty (ChapterTasteGate EquicontinuousCompletionUp) ∧
      (∀ h : BHist,
        equicontinuousCompletionDecodeBHist (equicontinuousCompletionEncodeBHist h) = h) ∧
      equicontinuousCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨equicontinuousCompletionBHistCarrier⟩
  constructor
  · exact ⟨equicontinuousCompletionChapterTasteGate⟩
  constructor
  · exact EquicontinuousCompletionTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.EquicontinuousCompletionUp
