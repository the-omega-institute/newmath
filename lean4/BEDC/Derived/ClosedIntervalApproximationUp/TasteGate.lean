import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedIntervalApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedIntervalApproximationUp : Type where
  | mk (I K Q D S R L U W H C P N : BHist) : ClosedIntervalApproximationUp
  deriving DecidableEq

def closedIntervalApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedIntervalApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedIntervalApproximationEncodeBHist h

def closedIntervalApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedIntervalApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedIntervalApproximationDecodeBHist tail)

private theorem ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedIntervalApproximationToEventFlow :
    ClosedIntervalApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalApproximationUp.mk I K Q D S R L U W H C P N =>
      [closedIntervalApproximationEncodeBHist I,
        closedIntervalApproximationEncodeBHist K,
        closedIntervalApproximationEncodeBHist Q,
        closedIntervalApproximationEncodeBHist D,
        closedIntervalApproximationEncodeBHist S,
        closedIntervalApproximationEncodeBHist R,
        closedIntervalApproximationEncodeBHist L,
        closedIntervalApproximationEncodeBHist U,
        closedIntervalApproximationEncodeBHist W,
        closedIntervalApproximationEncodeBHist H,
        closedIntervalApproximationEncodeBHist C,
        closedIntervalApproximationEncodeBHist P,
        closedIntervalApproximationEncodeBHist N]

private def closedIntervalApproximationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      closedIntervalApproximationEventAtDefault index rest

def closedIntervalApproximationFromEventFlow
    (ef : EventFlow) : Option ClosedIntervalApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedIntervalApproximationUp.mk
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 0 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 1 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 2 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 3 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 4 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 5 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 6 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 7 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 8 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 9 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 10 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 11 ef))
      (closedIntervalApproximationDecodeBHist
        (closedIntervalApproximationEventAtDefault 12 ef)))

private theorem ClosedIntervalApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedIntervalApproximationUp,
      closedIntervalApproximationFromEventFlow
        (closedIntervalApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I K Q D S R L U W H C P N =>
      change
        some
          (ClosedIntervalApproximationUp.mk
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist I))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist K))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist Q))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist D))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist S))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist R))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist L))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist U))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist W))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist H))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist C))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist P))
            (closedIntervalApproximationDecodeBHist
              (closedIntervalApproximationEncodeBHist N))) =
          some (ClosedIntervalApproximationUp.mk I K Q D S R L U W H C P N)
      rw [ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode I,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode K,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode Q,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode D,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode S,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode R,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode L,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode U,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode W,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode H,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode C,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode P,
        ClosedIntervalApproximationTasteGate_single_carrier_alignment_decode N]

private theorem ClosedIntervalApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedIntervalApproximationUp} :
    closedIntervalApproximationToEventFlow x =
        closedIntervalApproximationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalApproximationFromEventFlow
          (closedIntervalApproximationToEventFlow x) =
        closedIntervalApproximationFromEventFlow
          (closedIntervalApproximationToEventFlow y) :=
    congrArg closedIntervalApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedIntervalApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedIntervalApproximationTasteGate_single_carrier_alignment_round_trip y)))

instance closedIntervalApproximationBHistCarrier :
    BHistCarrier ClosedIntervalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedIntervalApproximationToEventFlow
  fromEventFlow := closedIntervalApproximationFromEventFlow

instance closedIntervalApproximationChapterTasteGate :
    ChapterTasteGate ClosedIntervalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedIntervalApproximationFromEventFlow
        (closedIntervalApproximationToEventFlow x) = some x
    exact ClosedIntervalApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedIntervalApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ClosedIntervalApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedIntervalApproximationChapterTasteGate

theorem ClosedIntervalApproximationTasteGate_single_carrier_alignment :
    ChapterTasteGate ClosedIntervalApproximationUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact closedIntervalApproximationChapterTasteGate

end BEDC.Derived.ClosedIntervalApproximationUp
