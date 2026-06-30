import BEDC.Derived.MetricReverseTriangleInequalityUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricReverseTriangleInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def metricReverseTriangleInequalityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricReverseTriangleInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricReverseTriangleInequalityEncodeBHist h

def metricReverseTriangleInequalityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricReverseTriangleInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricReverseTriangleInequalityDecodeBHist tail)

private theorem MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricReverseTriangleInequalityToEventFlow :
    BEDC.Derived.MetricReverseTriangleInequalityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (BEDC.Derived.metricReverseTriangleInequalityFields x).map
        metricReverseTriangleInequalityEncodeBHist

def metricReverseTriangleInequalityEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricReverseTriangleInequalityEventAt index rest

def metricReverseTriangleInequalityFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.MetricReverseTriangleInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.MetricReverseTriangleInequalityUp.mk
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 0 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 1 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 2 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 3 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 4 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 5 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 6 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 7 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 8 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 9 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 10 ef))
      (metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEventAt 11 ef)))

private theorem metricReverseTriangleInequality_round_trip :
    forall x : BEDC.Derived.MetricReverseTriangleInequalityUp,
      metricReverseTriangleInequalityFromEventFlow
        (metricReverseTriangleInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M DXZ DYZ G E W R S H C P N =>
      change
        some
          (BEDC.Derived.MetricReverseTriangleInequalityUp.mk
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist M))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist DXZ))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist DYZ))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist G))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist E))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist W))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist R))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist S))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist H))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist C))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist P))
            (metricReverseTriangleInequalityDecodeBHist
              (metricReverseTriangleInequalityEncodeBHist N))) =
          some
            (BEDC.Derived.MetricReverseTriangleInequalityUp.mk M DXZ DYZ G E W R S H C P N)
      rw [MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode M,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode DXZ,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode DYZ,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode G,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode E,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode W,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode R,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode S,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode H,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode C,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode P,
        MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode N]

private theorem metricReverseTriangleInequalityToEventFlow_injective
    {x y : BEDC.Derived.MetricReverseTriangleInequalityUp} :
    metricReverseTriangleInequalityToEventFlow x =
        metricReverseTriangleInequalityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricReverseTriangleInequalityFromEventFlow
          (metricReverseTriangleInequalityToEventFlow x) =
        metricReverseTriangleInequalityFromEventFlow
          (metricReverseTriangleInequalityToEventFlow y) :=
    congrArg metricReverseTriangleInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricReverseTriangleInequality_round_trip x).symm
      (Eq.trans hread (metricReverseTriangleInequality_round_trip y)))

private theorem metricReverseTriangleInequality_field_faithful :
    forall x y : BEDC.Derived.MetricReverseTriangleInequalityUp,
      BEDC.Derived.metricReverseTriangleInequalityFields x =
          BEDC.Derived.metricReverseTriangleInequalityFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ DXZ₁ DYZ₁ G₁ E₁ W₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ DXZ₂ DYZ₂ G₂ E₂ W₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance metricReverseTriangleInequalityBHistCarrier :
    BHistCarrier BEDC.Derived.MetricReverseTriangleInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricReverseTriangleInequalityToEventFlow
  fromEventFlow := metricReverseTriangleInequalityFromEventFlow

instance metricReverseTriangleInequalityChapterTasteGate :
    ChapterTasteGate BEDC.Derived.MetricReverseTriangleInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => metricReverseTriangleInequality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricReverseTriangleInequalityToEventFlow_injective heq)

instance metricReverseTriangleInequalityFieldFaithful :
    FieldFaithful BEDC.Derived.MetricReverseTriangleInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BEDC.Derived.metricReverseTriangleInequalityFields
  field_faithful := metricReverseTriangleInequality_field_faithful

instance metricReverseTriangleInequalityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BEDC.Derived.MetricReverseTriangleInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.MetricReverseTriangleInequalityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BEDC.Derived.MetricReverseTriangleInequalityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def metricReverseTriangleInequalityTasteGate :
    ChapterTasteGate BEDC.Derived.MetricReverseTriangleInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricReverseTriangleInequalityChapterTasteGate

theorem MetricReverseTriangleInequalityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metricReverseTriangleInequalityDecodeBHist
        (metricReverseTriangleInequalityEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.MetricReverseTriangleInequalityUp,
        metricReverseTriangleInequalityFromEventFlow
          (metricReverseTriangleInequalityToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.MetricReverseTriangleInequalityUp,
          metricReverseTriangleInequalityToEventFlow x =
              metricReverseTriangleInequalityToEventFlow y →
            x = y) ∧
          metricReverseTriangleInequalityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MetricReverseTriangleInequalityTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact metricReverseTriangleInequality_round_trip
    · constructor
      · intro x y heq
        exact metricReverseTriangleInequalityToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetricReverseTriangleInequalityUp
