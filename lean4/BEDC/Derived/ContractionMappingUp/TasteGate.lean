import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractionMappingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractionMappingUp : Type where
  | mk
      (metricRow distanceRow selfMap graphRow boundLedger modulusRow picardRoute transportRows
        routeRows provenance nameRow : BHist) :
      ContractionMappingUp
  deriving DecidableEq

def contractionMappingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contractionMappingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contractionMappingEncodeBHist h

def contractionMappingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contractionMappingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contractionMappingDecodeBHist tail)

private theorem contractionMappingDecodeEncodeBHist :
    ∀ h : BHist, contractionMappingDecodeBHist (contractionMappingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def contractionMappingFields : ContractionMappingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractionMappingUp.mk metricRow distanceRow selfMap graphRow boundLedger modulusRow
      picardRoute transportRows routeRows provenance nameRow =>
      [metricRow, distanceRow, selfMap, graphRow, boundLedger, modulusRow, picardRoute,
        transportRows, routeRows, provenance, nameRow]

def contractionMappingToEventFlow : ContractionMappingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contractionMappingFields x).map contractionMappingEncodeBHist

private def contractionMappingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contractionMappingEventAt index rest

def contractionMappingFromEventFlow (ef : EventFlow) : Option ContractionMappingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContractionMappingUp.mk
      (contractionMappingDecodeBHist (contractionMappingEventAt 0 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 1 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 2 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 3 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 4 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 5 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 6 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 7 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 8 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 9 ef))
      (contractionMappingDecodeBHist (contractionMappingEventAt 10 ef)))

private theorem contractionMapping_round_trip (x : ContractionMappingUp) :
    contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk metricRow distanceRow selfMap graphRow boundLedger modulusRow picardRoute transportRows
      routeRows provenance nameRow =>
      change
        some
          (ContractionMappingUp.mk
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist metricRow))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist distanceRow))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist selfMap))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist graphRow))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist boundLedger))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist modulusRow))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist picardRoute))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist transportRows))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist routeRows))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist provenance))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist nameRow))) =
          some
            (ContractionMappingUp.mk metricRow distanceRow selfMap graphRow boundLedger
              modulusRow picardRoute transportRows routeRows provenance nameRow)
      rw [contractionMappingDecodeEncodeBHist metricRow,
        contractionMappingDecodeEncodeBHist distanceRow,
        contractionMappingDecodeEncodeBHist selfMap,
        contractionMappingDecodeEncodeBHist graphRow,
        contractionMappingDecodeEncodeBHist boundLedger,
        contractionMappingDecodeEncodeBHist modulusRow,
        contractionMappingDecodeEncodeBHist picardRoute,
        contractionMappingDecodeEncodeBHist transportRows,
        contractionMappingDecodeEncodeBHist routeRows,
        contractionMappingDecodeEncodeBHist provenance,
        contractionMappingDecodeEncodeBHist nameRow]

private theorem contractionMappingToEventFlow_injective {x y : ContractionMappingUp} :
    contractionMappingToEventFlow x = contractionMappingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractionMappingFromEventFlow (contractionMappingToEventFlow x) =
        contractionMappingFromEventFlow (contractionMappingToEventFlow y) :=
    congrArg contractionMappingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (contractionMapping_round_trip x).symm
      (Eq.trans hread (contractionMapping_round_trip y)))

instance contractionMappingBHistCarrier : BHistCarrier ContractionMappingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractionMappingToEventFlow
  fromEventFlow := contractionMappingFromEventFlow

instance contractionMappingChapterTasteGate : ChapterTasteGate ContractionMappingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x
    exact contractionMapping_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contractionMappingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ContractionMappingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contractionMappingChapterTasteGate

theorem ContractionMappingTasteGate_single_carrier_alignment :
    (∀ h : BHist, contractionMappingDecodeBHist (contractionMappingEncodeBHist h) = h) ∧
      (∀ x : ContractionMappingUp,
        contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x) ∧
        (∀ x y : ContractionMappingUp,
          contractionMappingToEventFlow x = contractionMappingToEventFlow y → x = y) ∧
          contractionMappingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact contractionMappingDecodeEncodeBHist
  · constructor
    · exact contractionMapping_round_trip
    · constructor
      · intro x y heq
        exact contractionMappingToEventFlow_injective heq
      · rfl

end BEDC.Derived.ContractionMappingUp.TasteGate
