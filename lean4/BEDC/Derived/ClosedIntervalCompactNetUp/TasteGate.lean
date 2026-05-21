import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedIntervalCompactNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedIntervalCompactNetUp : Type where
  | mk
      (interval mesh finiteNet completionBoundary streamWindow regSeqReadback realSeal
        compactLedger transportRows continuationRows provenance localName : BHist) :
      ClosedIntervalCompactNetUp
  deriving DecidableEq

def closedIntervalCompactNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedIntervalCompactNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedIntervalCompactNetEncodeBHist h

def closedIntervalCompactNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedIntervalCompactNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedIntervalCompactNetDecodeBHist tail)

private theorem ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      closedIntervalCompactNetDecodeBHist (closedIntervalCompactNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedIntervalCompactNetFields : ClosedIntervalCompactNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalCompactNetUp.mk interval mesh finiteNet completionBoundary streamWindow
      regSeqReadback realSeal compactLedger transportRows continuationRows provenance localName =>
      [interval, mesh, finiteNet, completionBoundary, streamWindow, regSeqReadback, realSeal,
        compactLedger, transportRows, continuationRows, provenance, localName]

def closedIntervalCompactNetToEventFlow : ClosedIntervalCompactNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedIntervalCompactNetFields x).map closedIntervalCompactNetEncodeBHist

private def ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault index rest

def closedIntervalCompactNetFromEventFlow
    (ef : EventFlow) : Option ClosedIntervalCompactNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedIntervalCompactNetUp.mk
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (closedIntervalCompactNetDecodeBHist (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

private theorem ClosedIntervalCompactNetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedIntervalCompactNetUp,
      closedIntervalCompactNetFromEventFlow (closedIntervalCompactNetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval mesh finiteNet completionBoundary streamWindow regSeqReadback realSeal
      compactLedger transportRows continuationRows provenance localName =>
      change
        some
          (ClosedIntervalCompactNetUp.mk
            (closedIntervalCompactNetDecodeBHist (closedIntervalCompactNetEncodeBHist interval))
            (closedIntervalCompactNetDecodeBHist (closedIntervalCompactNetEncodeBHist mesh))
            (closedIntervalCompactNetDecodeBHist (closedIntervalCompactNetEncodeBHist finiteNet))
            (closedIntervalCompactNetDecodeBHist
              (closedIntervalCompactNetEncodeBHist completionBoundary))
            (closedIntervalCompactNetDecodeBHist
              (closedIntervalCompactNetEncodeBHist streamWindow))
            (closedIntervalCompactNetDecodeBHist
              (closedIntervalCompactNetEncodeBHist regSeqReadback))
            (closedIntervalCompactNetDecodeBHist (closedIntervalCompactNetEncodeBHist realSeal))
            (closedIntervalCompactNetDecodeBHist
              (closedIntervalCompactNetEncodeBHist compactLedger))
            (closedIntervalCompactNetDecodeBHist
              (closedIntervalCompactNetEncodeBHist transportRows))
            (closedIntervalCompactNetDecodeBHist
              (closedIntervalCompactNetEncodeBHist continuationRows))
            (closedIntervalCompactNetDecodeBHist
              (closedIntervalCompactNetEncodeBHist provenance))
            (closedIntervalCompactNetDecodeBHist
              (closedIntervalCompactNetEncodeBHist localName))) =
          some
            (ClosedIntervalCompactNetUp.mk interval mesh finiteNet completionBoundary
              streamWindow regSeqReadback realSeal compactLedger transportRows continuationRows
              provenance localName)
      rw [ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode interval,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode mesh,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode finiteNet,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode
          completionBoundary,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode streamWindow,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode regSeqReadback,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode realSeal,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode compactLedger,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode transportRows,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode continuationRows,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode provenance,
        ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode localName]

private theorem ClosedIntervalCompactNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedIntervalCompactNetUp} :
    closedIntervalCompactNetToEventFlow x = closedIntervalCompactNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalCompactNetFromEventFlow (closedIntervalCompactNetToEventFlow x) =
        closedIntervalCompactNetFromEventFlow (closedIntervalCompactNetToEventFlow y) :=
    congrArg closedIntervalCompactNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_round_trip y)))

instance closedIntervalCompactNetBHistCarrier : BHistCarrier ClosedIntervalCompactNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedIntervalCompactNetToEventFlow
  fromEventFlow := closedIntervalCompactNetFromEventFlow

instance closedIntervalCompactNetChapterTasteGate :
    ChapterTasteGate ClosedIntervalCompactNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedIntervalCompactNetFromEventFlow (closedIntervalCompactNetToEventFlow x) = some x
    exact ClosedIntervalCompactNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedIntervalCompactNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ClosedIntervalCompactNetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedIntervalCompactNetDecodeBHist (closedIntervalCompactNetEncodeBHist h) = h) ∧
      (∀ x : ClosedIntervalCompactNetUp,
        closedIntervalCompactNetFromEventFlow (closedIntervalCompactNetToEventFlow x) =
          some x) ∧
        (∀ x y : ClosedIntervalCompactNetUp,
          closedIntervalCompactNetToEventFlow x = closedIntervalCompactNetToEventFlow y →
            x = y) ∧
          closedIntervalCompactNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ClosedIntervalCompactNetTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact ClosedIntervalCompactNetTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact ClosedIntervalCompactNetTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.ClosedIntervalCompactNetUp
