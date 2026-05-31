import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricProjectionUp : Type where
  | mk
      (hilbertSource convexSource distanceLedger infimumBudget minimizingWindow
        endpoint transport replay provenance localCert : BHist) :
      MetricProjectionUp
  deriving DecidableEq

def metricProjectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricProjectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricProjectionEncodeBHist h

def metricProjectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricProjectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricProjectionDecodeBHist tail)

private theorem MetricProjectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, metricProjectionDecodeBHist (metricProjectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricProjectionFields : MetricProjectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricProjectionUp.mk hilbertSource convexSource distanceLedger infimumBudget
      minimizingWindow endpoint transport replay provenance localCert =>
      [hilbertSource, convexSource, distanceLedger, infimumBudget, minimizingWindow,
        endpoint, transport, replay, provenance, localCert]

def metricProjectionToEventFlow : MetricProjectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricProjectionFields x).map metricProjectionEncodeBHist

private def metricProjectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricProjectionEventAtDefault index rest

def metricProjectionFromEventFlow : EventFlow → Option MetricProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetricProjectionUp.mk
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 0 ef))
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 1 ef))
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 2 ef))
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 3 ef))
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 4 ef))
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 5 ef))
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 6 ef))
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 7 ef))
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 8 ef))
        (metricProjectionDecodeBHist (metricProjectionEventAtDefault 9 ef)))

private theorem MetricProjectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricProjectionUp,
      metricProjectionFromEventFlow (metricProjectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk hilbertSource convexSource distanceLedger infimumBudget minimizingWindow endpoint
      transport replay provenance localCert =>
      change
        some
          (MetricProjectionUp.mk
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist hilbertSource))
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist convexSource))
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist distanceLedger))
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist infimumBudget))
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist minimizingWindow))
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist endpoint))
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist transport))
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist replay))
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist provenance))
            (metricProjectionDecodeBHist (metricProjectionEncodeBHist localCert))) =
          some
            (MetricProjectionUp.mk hilbertSource convexSource distanceLedger infimumBudget
              minimizingWindow endpoint transport replay provenance localCert)
      rw [MetricProjectionTasteGate_single_carrier_alignment_decode hilbertSource,
        MetricProjectionTasteGate_single_carrier_alignment_decode convexSource,
        MetricProjectionTasteGate_single_carrier_alignment_decode distanceLedger,
        MetricProjectionTasteGate_single_carrier_alignment_decode infimumBudget,
        MetricProjectionTasteGate_single_carrier_alignment_decode minimizingWindow,
        MetricProjectionTasteGate_single_carrier_alignment_decode endpoint,
        MetricProjectionTasteGate_single_carrier_alignment_decode transport,
        MetricProjectionTasteGate_single_carrier_alignment_decode replay,
        MetricProjectionTasteGate_single_carrier_alignment_decode provenance,
        MetricProjectionTasteGate_single_carrier_alignment_decode localCert]

theorem metricProjectionToEventFlow_injective {x y : MetricProjectionUp} :
    metricProjectionToEventFlow x = metricProjectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricProjectionFromEventFlow (metricProjectionToEventFlow x) =
        metricProjectionFromEventFlow (metricProjectionToEventFlow y) :=
    congrArg metricProjectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricProjectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricProjectionTasteGate_single_carrier_alignment_round_trip y)))

instance metricProjectionBHistCarrier : BHistCarrier MetricProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricProjectionToEventFlow
  fromEventFlow := metricProjectionFromEventFlow

instance metricProjectionChapterTasteGate : ChapterTasteGate MetricProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricProjectionFromEventFlow (metricProjectionToEventFlow x) = some x
    exact MetricProjectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricProjectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetricProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricProjectionChapterTasteGate

theorem MetricProjectionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier MetricProjectionUp) ∧
      Nonempty (ChapterTasteGate MetricProjectionUp) ∧
      (∀ x : MetricProjectionUp,
        metricProjectionFromEventFlow (metricProjectionToEventFlow x) = some x) ∧
      (∀ x y : MetricProjectionUp,
        metricProjectionToEventFlow x = metricProjectionToEventFlow y → x = y) ∧
      metricProjectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨metricProjectionBHistCarrier⟩
  constructor
  · exact ⟨metricProjectionChapterTasteGate⟩
  constructor
  · exact MetricProjectionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact metricProjectionToEventFlow_injective heq
  · rfl

end BEDC.Derived.MetricProjectionUp
