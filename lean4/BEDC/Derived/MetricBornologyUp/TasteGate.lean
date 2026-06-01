import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricBornologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricBornologyUp : Type where
  | mk
      (metricSpace boundedSubset center radius metricBall finiteUnion hereditary handoff
        transport replay provenance localName : BHist) :
      MetricBornologyUp
  deriving DecidableEq

def metricBornologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricBornologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricBornologyEncodeBHist h

def metricBornologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricBornologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricBornologyDecodeBHist tail)

private theorem MetricBornologyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, metricBornologyDecodeBHist (metricBornologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def MetricBornologyTasteGate_single_carrier_alignment_fields :
    MetricBornologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricBornologyUp.mk metricSpace boundedSubset center radius metricBall finiteUnion
      hereditary handoff transport replay provenance localName =>
      [metricSpace, boundedSubset, center, radius, metricBall, finiteUnion, hereditary, handoff,
        transport, replay, provenance, localName]

def MetricBornologyTasteGate_single_carrier_alignment_toEventFlow :
    MetricBornologyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (MetricBornologyTasteGate_single_carrier_alignment_fields x).map
      metricBornologyEncodeBHist

private def MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault index rest

def MetricBornologyTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option MetricBornologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetricBornologyUp.mk
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
        (metricBornologyDecodeBHist
          (MetricBornologyTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

def MetricBornologyTasteGate_single_carrier_alignment_carrier :
    BHistCarrier MetricBornologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MetricBornologyTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := MetricBornologyTasteGate_single_carrier_alignment_fromEventFlow

instance MetricBornologyTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier MetricBornologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  MetricBornologyTasteGate_single_carrier_alignment_carrier

private theorem MetricBornologyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricBornologyUp,
      MetricBornologyTasteGate_single_carrier_alignment_fromEventFlow
          (MetricBornologyTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk metricSpace boundedSubset center radius metricBall finiteUnion hereditary handoff
      transport replay provenance localName =>
      change
        some
            (MetricBornologyUp.mk
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist metricSpace))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist boundedSubset))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist center))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist radius))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist metricBall))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist finiteUnion))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist hereditary))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist handoff))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist transport))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist replay))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist provenance))
              (metricBornologyDecodeBHist (metricBornologyEncodeBHist localName))) =
          some
            (MetricBornologyUp.mk metricSpace boundedSubset center radius metricBall finiteUnion
              hereditary handoff transport replay provenance localName)
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode metricSpace]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode boundedSubset]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode center]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode radius]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode metricBall]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode finiteUnion]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode hereditary]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode handoff]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode transport]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode replay]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [MetricBornologyTasteGate_single_carrier_alignment_decode_encode localName]

private theorem MetricBornologyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricBornologyUp} :
    MetricBornologyTasteGate_single_carrier_alignment_toEventFlow x =
        MetricBornologyTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          MetricBornologyTasteGate_single_carrier_alignment_fromEventFlow
            (MetricBornologyTasteGate_single_carrier_alignment_toEventFlow x) :=
        (MetricBornologyTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          MetricBornologyTasteGate_single_carrier_alignment_fromEventFlow
            (MetricBornologyTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg MetricBornologyTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := MetricBornologyTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def MetricBornologyTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate MetricBornologyUp
      MetricBornologyTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      MetricBornologyTasteGate_single_carrier_alignment_fromEventFlow
          (MetricBornologyTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact MetricBornologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricBornologyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance MetricBornologyTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate MetricBornologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  MetricBornologyTasteGate_single_carrier_alignment_gate

theorem MetricBornologyTasteGate_single_carrier_alignment :
    (forall h : BHist, metricBornologyDecodeBHist (metricBornologyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetricBornologyUp) ∧
      Nonempty (ChapterTasteGate MetricBornologyUp) ∧
      metricBornologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetricBornologyTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨MetricBornologyTasteGate_single_carrier_alignment_carrier⟩,
        ⟨⟨MetricBornologyTasteGate_single_carrier_alignment_gate⟩, rfl⟩⟩⟩

end BEDC.Derived.MetricBornologyUp
