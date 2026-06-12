import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionLeftAdjointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionLeftAdjointUp : Type where
  | mk (M D A J R E H C P N : BHist) : MetricCompletionLeftAdjointUp
  deriving DecidableEq

def metricCompletionLeftAdjointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionLeftAdjointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionLeftAdjointEncodeBHist h

def metricCompletionLeftAdjointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionLeftAdjointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionLeftAdjointDecodeBHist tail)

private theorem MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metricCompletionLeftAdjointDecodeBHist
        (metricCompletionLeftAdjointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionLeftAdjointFields :
    MetricCompletionLeftAdjointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionLeftAdjointUp.mk M D A J R E H C P N =>
      [M, D, A, J, R, E, H, C, P, N]

def metricCompletionLeftAdjointToEventFlow :
    MetricCompletionLeftAdjointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metricCompletionLeftAdjointFields x).map metricCompletionLeftAdjointEncodeBHist

private def metricCompletionLeftAdjointEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionLeftAdjointEventAt index rest

def metricCompletionLeftAdjointFromEventFlow
    (ef : EventFlow) : Option MetricCompletionLeftAdjointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionLeftAdjointUp.mk
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 0 ef))
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 1 ef))
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 2 ef))
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 3 ef))
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 4 ef))
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 5 ef))
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 6 ef))
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 7 ef))
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 8 ef))
      (metricCompletionLeftAdjointDecodeBHist (metricCompletionLeftAdjointEventAt 9 ef)))

private theorem MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_round_trip
    (x : MetricCompletionLeftAdjointUp) :
    metricCompletionLeftAdjointFromEventFlow
        (metricCompletionLeftAdjointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M D A J R E H C P N =>
      change
        some
            (MetricCompletionLeftAdjointUp.mk
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist M))
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist D))
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist A))
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist J))
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist R))
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist E))
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist H))
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist C))
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist P))
              (metricCompletionLeftAdjointDecodeBHist
                (metricCompletionLeftAdjointEncodeBHist N))) =
          some (MetricCompletionLeftAdjointUp.mk M D A J R E H C P N)
      rw [MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode M,
        MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode D,
        MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode A,
        MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode J,
        MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode R,
        MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode E,
        MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionLeftAdjointUp} :
    metricCompletionLeftAdjointToEventFlow x =
        metricCompletionLeftAdjointToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionLeftAdjointFromEventFlow
          (metricCompletionLeftAdjointToEventFlow x) =
        metricCompletionLeftAdjointFromEventFlow
          (metricCompletionLeftAdjointToEventFlow y) :=
    congrArg metricCompletionLeftAdjointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_round_trip y)))

instance metricCompletionLeftAdjointBHistCarrier :
    BHistCarrier MetricCompletionLeftAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionLeftAdjointToEventFlow
  fromEventFlow := metricCompletionLeftAdjointFromEventFlow

instance metricCompletionLeftAdjointChapterTasteGate :
    ChapterTasteGate MetricCompletionLeftAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionLeftAdjointFromEventFlow
          (metricCompletionLeftAdjointToEventFlow x) = some x
    exact MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def metricCompletionLeftAdjointTasteGate :
    ChapterTasteGate MetricCompletionLeftAdjointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionLeftAdjointChapterTasteGate

theorem MetricCompletionLeftAdjointTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metricCompletionLeftAdjointDecodeBHist
        (metricCompletionLeftAdjointEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetricCompletionLeftAdjointUp) ∧
        Nonempty (ChapterTasteGate MetricCompletionLeftAdjointUp) ∧
          metricCompletionLeftAdjointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode_encode,
      ⟨metricCompletionLeftAdjointBHistCarrier⟩,
      ⟨metricCompletionLeftAdjointChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MetricCompletionLeftAdjointUp
