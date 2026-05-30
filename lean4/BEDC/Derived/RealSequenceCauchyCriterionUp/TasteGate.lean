import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSequenceCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSequenceCauchyCriterionUp : Type where
  | mk :
      (limitRow streamSchedule regularReadback dyadicLedger cauchyClassifier comparisonBoundary
        transport replay provenance localCert : BHist) →
      RealSequenceCauchyCriterionUp
  deriving DecidableEq

def realSequenceCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSequenceCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSequenceCauchyCriterionEncodeBHist h

def realSequenceCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSequenceCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSequenceCauchyCriterionDecodeBHist tail)

theorem RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realSequenceCauchyCriterionFields : RealSequenceCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSequenceCauchyCriterionUp.mk limitRow streamSchedule regularReadback dyadicLedger
      cauchyClassifier comparisonBoundary transport replay provenance localCert =>
      [limitRow, streamSchedule, regularReadback, dyadicLedger, cauchyClassifier,
        comparisonBoundary, transport, replay, provenance, localCert]

def realSequenceCauchyCriterionToEventFlow : RealSequenceCauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realSequenceCauchyCriterionEncodeBHist (realSequenceCauchyCriterionFields x)

private def realSequenceCauchyCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realSequenceCauchyCriterionEventAtDefault index rest

def realSequenceCauchyCriterionFromEventFlow :
    EventFlow → Option RealSequenceCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealSequenceCauchyCriterionUp.mk
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 0 ef))
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 1 ef))
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 2 ef))
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 3 ef))
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 4 ef))
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 5 ef))
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 6 ef))
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 7 ef))
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 8 ef))
        (realSequenceCauchyCriterionDecodeBHist
          (realSequenceCauchyCriterionEventAtDefault 9 ef)))

private theorem realSequenceCauchyCriterion_round_trip :
    ∀ x : RealSequenceCauchyCriterionUp,
      realSequenceCauchyCriterionFromEventFlow
          (realSequenceCauchyCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk limitRow streamSchedule regularReadback dyadicLedger cauchyClassifier comparisonBoundary
      transport replay provenance localCert =>
      change
        some
          (RealSequenceCauchyCriterionUp.mk
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist limitRow))
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist streamSchedule))
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist regularReadback))
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist dyadicLedger))
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist cauchyClassifier))
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist comparisonBoundary))
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist transport))
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist replay))
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist provenance))
            (realSequenceCauchyCriterionDecodeBHist
              (realSequenceCauchyCriterionEncodeBHist localCert))) =
          some
            (RealSequenceCauchyCriterionUp.mk limitRow streamSchedule regularReadback
              dyadicLedger cauchyClassifier comparisonBoundary transport replay provenance
              localCert)
      rw [RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode limitRow,
        RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode streamSchedule,
        RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode
          regularReadback,
        RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode dyadicLedger,
        RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode
          cauchyClassifier,
        RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode
          comparisonBoundary,
        RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode transport,
        RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode replay,
        RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode provenance,
        RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode localCert]

private theorem realSequenceCauchyCriterionToEventFlow_injective
    {x y : RealSequenceCauchyCriterionUp} :
    realSequenceCauchyCriterionToEventFlow x =
      realSequenceCauchyCriterionToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSequenceCauchyCriterionFromEventFlow (realSequenceCauchyCriterionToEventFlow x) =
        realSequenceCauchyCriterionFromEventFlow (realSequenceCauchyCriterionToEventFlow y) :=
    congrArg realSequenceCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realSequenceCauchyCriterion_round_trip x).symm
      (Eq.trans hread (realSequenceCauchyCriterion_round_trip y)))

instance realSequenceCauchyCriterionBHistCarrier :
    BHistCarrier RealSequenceCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSequenceCauchyCriterionToEventFlow
  fromEventFlow := realSequenceCauchyCriterionFromEventFlow

instance realSequenceCauchyCriterionChapterTasteGate :
    ChapterTasteGate RealSequenceCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realSequenceCauchyCriterionFromEventFlow
          (realSequenceCauchyCriterionToEventFlow x) =
        some x
    exact realSequenceCauchyCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSequenceCauchyCriterionToEventFlow_injective heq)

theorem RealSequenceCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        realSequenceCauchyCriterionDecodeBHist
            (realSequenceCauchyCriterionEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier RealSequenceCauchyCriterionUp) ∧
      Nonempty (ChapterTasteGate RealSequenceCauchyCriterionUp) ∧
      realSequenceCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealSequenceCauchyCriterionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact Nonempty.intro realSequenceCauchyCriterionBHistCarrier
    · constructor
      · exact Nonempty.intro realSequenceCauchyCriterionChapterTasteGate
      · rfl

end BEDC.Derived.RealSequenceCauchyCriterionUp
