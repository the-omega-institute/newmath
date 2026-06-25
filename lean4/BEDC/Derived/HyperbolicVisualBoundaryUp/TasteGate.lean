import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicVisualBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicVisualBoundaryUp : Type where
  | mk
      (diskReadout boundaryShadow busemann visualMetric boundaryTransport provenance
        transport replay nameCert : BHist) :
      HyperbolicVisualBoundaryUp
  deriving DecidableEq

def hyperbolicVisualBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicVisualBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicVisualBoundaryEncodeBHist h

def hyperbolicVisualBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicVisualBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicVisualBoundaryDecodeBHist tail)

private theorem hyperbolicVisualBoundaryDecode_encode_bhist :
    forall h : BHist,
      hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hyperbolicVisualBoundaryFields : HyperbolicVisualBoundaryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicVisualBoundaryUp.mk diskReadout boundaryShadow busemann visualMetric
      boundaryTransport provenance transport replay nameCert =>
      [diskReadout, boundaryShadow, busemann, visualMetric, boundaryTransport, provenance,
        transport, replay, nameCert]

def hyperbolicVisualBoundaryToEventFlow : HyperbolicVisualBoundaryUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hyperbolicVisualBoundaryFields x).map hyperbolicVisualBoundaryEncodeBHist

private def hyperbolicVisualBoundaryEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      hyperbolicVisualBoundaryEventAtDefault index rest

def hyperbolicVisualBoundaryFromEventFlow (ef : EventFlow) :
    Option HyperbolicVisualBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicVisualBoundaryUp.mk
      (hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEventAtDefault 0 ef))
      (hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEventAtDefault 1 ef))
      (hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEventAtDefault 2 ef))
      (hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEventAtDefault 3 ef))
      (hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEventAtDefault 4 ef))
      (hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEventAtDefault 5 ef))
      (hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEventAtDefault 6 ef))
      (hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEventAtDefault 7 ef))
      (hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEventAtDefault 8 ef)))

private theorem hyperbolicVisualBoundary_round_trip :
    forall x : HyperbolicVisualBoundaryUp,
      hyperbolicVisualBoundaryFromEventFlow (hyperbolicVisualBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk diskReadout boundaryShadow busemann visualMetric boundaryTransport provenance
      transport replay nameCert =>
      change
        some
          (HyperbolicVisualBoundaryUp.mk
            (hyperbolicVisualBoundaryDecodeBHist
              (hyperbolicVisualBoundaryEncodeBHist diskReadout))
            (hyperbolicVisualBoundaryDecodeBHist
              (hyperbolicVisualBoundaryEncodeBHist boundaryShadow))
            (hyperbolicVisualBoundaryDecodeBHist
              (hyperbolicVisualBoundaryEncodeBHist busemann))
            (hyperbolicVisualBoundaryDecodeBHist
              (hyperbolicVisualBoundaryEncodeBHist visualMetric))
            (hyperbolicVisualBoundaryDecodeBHist
              (hyperbolicVisualBoundaryEncodeBHist boundaryTransport))
            (hyperbolicVisualBoundaryDecodeBHist
              (hyperbolicVisualBoundaryEncodeBHist provenance))
            (hyperbolicVisualBoundaryDecodeBHist
              (hyperbolicVisualBoundaryEncodeBHist transport))
            (hyperbolicVisualBoundaryDecodeBHist
              (hyperbolicVisualBoundaryEncodeBHist replay))
            (hyperbolicVisualBoundaryDecodeBHist
              (hyperbolicVisualBoundaryEncodeBHist nameCert))) =
          some
            (HyperbolicVisualBoundaryUp.mk diskReadout boundaryShadow busemann visualMetric
              boundaryTransport provenance transport replay nameCert)
      rw [hyperbolicVisualBoundaryDecode_encode_bhist diskReadout,
        hyperbolicVisualBoundaryDecode_encode_bhist boundaryShadow,
        hyperbolicVisualBoundaryDecode_encode_bhist busemann,
        hyperbolicVisualBoundaryDecode_encode_bhist visualMetric,
        hyperbolicVisualBoundaryDecode_encode_bhist boundaryTransport,
        hyperbolicVisualBoundaryDecode_encode_bhist provenance,
        hyperbolicVisualBoundaryDecode_encode_bhist transport,
        hyperbolicVisualBoundaryDecode_encode_bhist replay,
        hyperbolicVisualBoundaryDecode_encode_bhist nameCert]

private theorem hyperbolicVisualBoundaryToEventFlow_injective
    {x y : HyperbolicVisualBoundaryUp} :
    hyperbolicVisualBoundaryToEventFlow x = hyperbolicVisualBoundaryToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicVisualBoundaryFromEventFlow (hyperbolicVisualBoundaryToEventFlow x) =
        hyperbolicVisualBoundaryFromEventFlow (hyperbolicVisualBoundaryToEventFlow y) :=
    congrArg hyperbolicVisualBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperbolicVisualBoundary_round_trip x).symm
      (Eq.trans hread (hyperbolicVisualBoundary_round_trip y)))

private theorem hyperbolicVisualBoundaryFieldFaithfulProof :
    forall x y : HyperbolicVisualBoundaryUp,
      hyperbolicVisualBoundaryFields x = hyperbolicVisualBoundaryFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk diskReadout boundaryShadow busemann visualMetric boundaryTransport provenance
      transport replay nameCert =>
      cases y with
      | mk diskReadout' boundaryShadow' busemann' visualMetric' boundaryTransport'
          provenance' transport' replay' nameCert' =>
          cases hfields
          rfl

instance hyperbolicVisualBoundaryBHistCarrier : BHistCarrier HyperbolicVisualBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicVisualBoundaryToEventFlow
  fromEventFlow := hyperbolicVisualBoundaryFromEventFlow

instance hyperbolicVisualBoundaryChapterTasteGate :
    ChapterTasteGate HyperbolicVisualBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicVisualBoundaryFromEventFlow (hyperbolicVisualBoundaryToEventFlow x) =
        some x
    exact hyperbolicVisualBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperbolicVisualBoundaryToEventFlow_injective heq)

instance hyperbolicVisualBoundaryFieldFaithful :
    FieldFaithful HyperbolicVisualBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicVisualBoundaryFields
  field_faithful := hyperbolicVisualBoundaryFieldFaithfulProof

instance hyperbolicVisualBoundaryNontrivial :
    BEDC.Meta.TasteGate.Nontrivial HyperbolicVisualBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicVisualBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicVisualBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HyperbolicVisualBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicVisualBoundaryChapterTasteGate

theorem HyperbolicVisualBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      hyperbolicVisualBoundaryDecodeBHist (hyperbolicVisualBoundaryEncodeBHist h) = h) /\
      (forall x : HyperbolicVisualBoundaryUp,
        hyperbolicVisualBoundaryFromEventFlow (hyperbolicVisualBoundaryToEventFlow x) =
          some x) /\
        (forall x y : HyperbolicVisualBoundaryUp,
          hyperbolicVisualBoundaryToEventFlow x = hyperbolicVisualBoundaryToEventFlow y ->
            x = y) /\
          hyperbolicVisualBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact hyperbolicVisualBoundaryDecode_encode_bhist
  · constructor
    · exact hyperbolicVisualBoundary_round_trip
    · constructor
      · intro x y heq
        have hread :
            hyperbolicVisualBoundaryFromEventFlow (hyperbolicVisualBoundaryToEventFlow x) =
              hyperbolicVisualBoundaryFromEventFlow (hyperbolicVisualBoundaryToEventFlow y) :=
          congrArg hyperbolicVisualBoundaryFromEventFlow heq
        exact Option.some.inj
          (Eq.trans (hyperbolicVisualBoundary_round_trip x).symm
            (Eq.trans hread (hyperbolicVisualBoundary_round_trip y)))
      · rfl

end BEDC.Derived.HyperbolicVisualBoundaryUp
