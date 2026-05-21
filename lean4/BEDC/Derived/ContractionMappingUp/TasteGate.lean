import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractionMappingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractionMappingUp : Type where
  | mk
      (metric distance selfMap graph bound modulus picardRoute transportRows continuationRows
        provenance localName : BHist) :
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

private theorem ContractionMappingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      contractionMappingDecodeBHist (contractionMappingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contractionMappingFields : ContractionMappingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractionMappingUp.mk metric distance selfMap graph bound modulus picardRoute
      transportRows continuationRows provenance localName =>
      [metric, distance, selfMap, graph, bound, modulus, picardRoute, transportRows,
        continuationRows, provenance, localName]

def contractionMappingToEventFlow : ContractionMappingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contractionMappingFields x).map contractionMappingEncodeBHist

private def ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault index rest

def contractionMappingFromEventFlow (ef : EventFlow) : Option ContractionMappingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContractionMappingUp.mk
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (contractionMappingDecodeBHist (ContractionMappingTasteGate_single_carrier_alignment_eventAtDefault 10 ef)))

private theorem ContractionMappingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContractionMappingUp,
      contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric distance selfMap graph bound modulus picardRoute transportRows continuationRows
      provenance localName =>
      change
        some
          (ContractionMappingUp.mk
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist metric))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist distance))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist selfMap))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist graph))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist bound))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist modulus))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist picardRoute))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist transportRows))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist continuationRows))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist provenance))
            (contractionMappingDecodeBHist (contractionMappingEncodeBHist localName))) =
          some
            (ContractionMappingUp.mk metric distance selfMap graph bound modulus picardRoute
              transportRows continuationRows provenance localName)
      rw [ContractionMappingTasteGate_single_carrier_alignment_decode_encode metric,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode distance,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode selfMap,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode graph,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode bound,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode modulus,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode picardRoute,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode transportRows,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode continuationRows,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode provenance,
        ContractionMappingTasteGate_single_carrier_alignment_decode_encode localName]

private theorem ContractionMappingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContractionMappingUp} :
    contractionMappingToEventFlow x = contractionMappingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractionMappingFromEventFlow (contractionMappingToEventFlow x) =
        contractionMappingFromEventFlow (contractionMappingToEventFlow y) :=
    congrArg contractionMappingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContractionMappingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ContractionMappingTasteGate_single_carrier_alignment_round_trip y)))

instance contractionMappingBHistCarrier : BHistCarrier ContractionMappingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractionMappingToEventFlow
  fromEventFlow := contractionMappingFromEventFlow

instance contractionMappingChapterTasteGate : ChapterTasteGate ContractionMappingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x
    exact ContractionMappingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContractionMappingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ContractionMappingTasteGate_single_carrier_alignment :
    (∀ h : BHist, contractionMappingDecodeBHist (contractionMappingEncodeBHist h) = h) ∧
      (∀ x : ContractionMappingUp,
        contractionMappingFromEventFlow (contractionMappingToEventFlow x) = some x) ∧
        (∀ x y : ContractionMappingUp,
          contractionMappingToEventFlow x = contractionMappingToEventFlow y → x = y) ∧
          contractionMappingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ContractionMappingTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact ContractionMappingTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact ContractionMappingTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.ContractionMappingUp
