import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GaugeLebesgueNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GaugeLebesgueNumberUp : Type where
  | mk
      (compactMetric gaugeCover cousinSubdivision finiteRadius rationalComparison transport replay
        provenance name : BHist) :
      GaugeLebesgueNumberUp
  deriving DecidableEq

def gaugeLebesgueNumberEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gaugeLebesgueNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gaugeLebesgueNumberEncodeBHist h

def gaugeLebesgueNumberDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gaugeLebesgueNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gaugeLebesgueNumberDecodeBHist tail)

private theorem gaugeLebesgueNumber_decode_encode_bhist :
    forall h : BHist,
      gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def gaugeLebesgueNumberFields : GaugeLebesgueNumberUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GaugeLebesgueNumberUp.mk compactMetric gaugeCover cousinSubdivision finiteRadius
      rationalComparison transport replay provenance name =>
      [compactMetric, gaugeCover, cousinSubdivision, finiteRadius, rationalComparison, transport,
        replay, provenance, name]

def gaugeLebesgueNumberToEventFlow : GaugeLebesgueNumberUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (gaugeLebesgueNumberFields x).map gaugeLebesgueNumberEncodeBHist

private def gaugeLebesgueNumberEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => gaugeLebesgueNumberEventAtDefault index rest

def gaugeLebesgueNumberFromEventFlow : EventFlow -> Option GaugeLebesgueNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (GaugeLebesgueNumberUp.mk
        (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEventAtDefault 0 ef))
        (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEventAtDefault 1 ef))
        (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEventAtDefault 2 ef))
        (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEventAtDefault 3 ef))
        (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEventAtDefault 4 ef))
        (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEventAtDefault 5 ef))
        (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEventAtDefault 6 ef))
        (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEventAtDefault 7 ef))
        (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEventAtDefault 8 ef)))

private theorem gaugeLebesgueNumber_round_trip :
    forall x : GaugeLebesgueNumberUp,
      gaugeLebesgueNumberFromEventFlow (gaugeLebesgueNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactMetric gaugeCover cousinSubdivision finiteRadius rationalComparison transport
      replay provenance name =>
      change
        some
          (GaugeLebesgueNumberUp.mk
            (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEncodeBHist compactMetric))
            (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEncodeBHist gaugeCover))
            (gaugeLebesgueNumberDecodeBHist
              (gaugeLebesgueNumberEncodeBHist cousinSubdivision))
            (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEncodeBHist finiteRadius))
            (gaugeLebesgueNumberDecodeBHist
              (gaugeLebesgueNumberEncodeBHist rationalComparison))
            (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEncodeBHist transport))
            (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEncodeBHist replay))
            (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEncodeBHist provenance))
            (gaugeLebesgueNumberDecodeBHist (gaugeLebesgueNumberEncodeBHist name))) =
          some
            (GaugeLebesgueNumberUp.mk compactMetric gaugeCover cousinSubdivision finiteRadius
              rationalComparison transport replay provenance name)
      rw [gaugeLebesgueNumber_decode_encode_bhist compactMetric,
        gaugeLebesgueNumber_decode_encode_bhist gaugeCover,
        gaugeLebesgueNumber_decode_encode_bhist cousinSubdivision,
        gaugeLebesgueNumber_decode_encode_bhist finiteRadius,
        gaugeLebesgueNumber_decode_encode_bhist rationalComparison,
        gaugeLebesgueNumber_decode_encode_bhist transport,
        gaugeLebesgueNumber_decode_encode_bhist replay,
        gaugeLebesgueNumber_decode_encode_bhist provenance,
        gaugeLebesgueNumber_decode_encode_bhist name]

private theorem gaugeLebesgueNumberToEventFlow_injective
    {x y : GaugeLebesgueNumberUp} :
    gaugeLebesgueNumberToEventFlow x = gaugeLebesgueNumberToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gaugeLebesgueNumberFromEventFlow (gaugeLebesgueNumberToEventFlow x) =
        gaugeLebesgueNumberFromEventFlow (gaugeLebesgueNumberToEventFlow y) :=
    congrArg gaugeLebesgueNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (gaugeLebesgueNumber_round_trip x).symm
      (Eq.trans hread (gaugeLebesgueNumber_round_trip y)))

private theorem gaugeLebesgueNumber_field_faithful :
    forall x y : GaugeLebesgueNumberUp,
      gaugeLebesgueNumberFields x = gaugeLebesgueNumberFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk compactMetric gaugeCover cousinSubdivision finiteRadius rationalComparison transport
      replay provenance name =>
      cases y with
      | mk compactMetric' gaugeCover' cousinSubdivision' finiteRadius' rationalComparison'
          transport' replay' provenance' name' =>
          cases hfields
          rfl

instance gaugeLebesgueNumberBHistCarrier : BHistCarrier GaugeLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gaugeLebesgueNumberToEventFlow
  fromEventFlow := gaugeLebesgueNumberFromEventFlow

instance gaugeLebesgueNumberChapterTasteGate :
    ChapterTasteGate GaugeLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gaugeLebesgueNumberFromEventFlow (gaugeLebesgueNumberToEventFlow x) = some x
    exact gaugeLebesgueNumber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (gaugeLebesgueNumberToEventFlow_injective heq)

instance gaugeLebesgueNumberFieldFaithful :
    FieldFaithful GaugeLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := gaugeLebesgueNumberFields
  field_faithful := gaugeLebesgueNumber_field_faithful

instance gaugeLebesgueNumberNontrivial :
    Nontrivial GaugeLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GaugeLebesgueNumberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GaugeLebesgueNumberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GaugeLebesgueNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gaugeLebesgueNumberChapterTasteGate

theorem GaugeLebesgueNumberTasteGate_single_carrier_alignment :
    (∀ h : BHist, gaugeLebesgueNumberDecodeBHist
      (gaugeLebesgueNumberEncodeBHist h) = h) ∧
      (∀ x : GaugeLebesgueNumberUp,
        gaugeLebesgueNumberFromEventFlow (gaugeLebesgueNumberToEventFlow x) = some x) ∧
        (∀ x y : GaugeLebesgueNumberUp,
          gaugeLebesgueNumberToEventFlow x = gaugeLebesgueNumberToEventFlow y -> x = y) ∧
          ∃ x : GaugeLebesgueNumberUp,
            x = GaugeLebesgueNumberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
              gaugeLebesgueNumberFromEventFlow (gaugeLebesgueNumberToEventFlow x) =
                some x := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact gaugeLebesgueNumber_decode_encode_bhist
  · constructor
    · exact gaugeLebesgueNumber_round_trip
    · constructor
      · intro x y heq
        exact gaugeLebesgueNumberToEventFlow_injective heq
      · refine ⟨GaugeLebesgueNumberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, ?_, ?_⟩
        · rfl
        · exact gaugeLebesgueNumber_round_trip _

end BEDC.Derived.GaugeLebesgueNumberUp
