import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LayeredRelationFailureBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LayeredRelationFailureBoundaryUp : Type where
  | mk
      (relation exactness failureBoundary weakening gate transport route provenance name :
        BHist) :
      LayeredRelationFailureBoundaryUp
  deriving DecidableEq

def layeredRelationFailureBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: layeredRelationFailureBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: layeredRelationFailureBoundaryEncodeBHist h

def layeredRelationFailureBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (layeredRelationFailureBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (layeredRelationFailureBoundaryDecodeBHist tail)

private theorem layeredRelationFailureBoundary_decode_encode_bhist :
    ∀ h : BHist,
      layeredRelationFailureBoundaryDecodeBHist
        (layeredRelationFailureBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem layeredRelationFailureBoundary_mk_congr
    {relation₁ relation₂ exactness₁ exactness₂ failureBoundary₁ failureBoundary₂
      weakening₁ weakening₂ gate₁ gate₂ transport₁ transport₂ route₁ route₂ provenance₁
      provenance₂ name₁ name₂ : BHist}
    (hRelation : relation₁ = relation₂)
    (hExactness : exactness₁ = exactness₂)
    (hFailureBoundary : failureBoundary₁ = failureBoundary₂)
    (hWeakening : weakening₁ = weakening₂)
    (hGate : gate₁ = gate₂)
    (hTransport : transport₁ = transport₂)
    (hRoute : route₁ = route₂)
    (hProvenance : provenance₁ = provenance₂)
    (hName : name₁ = name₂) :
    LayeredRelationFailureBoundaryUp.mk relation₁ exactness₁ failureBoundary₁ weakening₁
        gate₁ transport₁ route₁ provenance₁ name₁ =
      LayeredRelationFailureBoundaryUp.mk relation₂ exactness₂ failureBoundary₂ weakening₂
        gate₂ transport₂ route₂ provenance₂ name₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRelation
  cases hExactness
  cases hFailureBoundary
  cases hWeakening
  cases hGate
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

private def layeredRelationFailureBoundaryDecodePacket
    (relation exactness failureBoundary weakening gate transport route provenance name :
      RawEvent) :
    LayeredRelationFailureBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  LayeredRelationFailureBoundaryUp.mk
    (layeredRelationFailureBoundaryDecodeBHist relation)
    (layeredRelationFailureBoundaryDecodeBHist exactness)
    (layeredRelationFailureBoundaryDecodeBHist failureBoundary)
    (layeredRelationFailureBoundaryDecodeBHist weakening)
    (layeredRelationFailureBoundaryDecodeBHist gate)
    (layeredRelationFailureBoundaryDecodeBHist transport)
    (layeredRelationFailureBoundaryDecodeBHist route)
    (layeredRelationFailureBoundaryDecodeBHist provenance)
    (layeredRelationFailureBoundaryDecodeBHist name)

private def layeredRelationFailureBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => layeredRelationFailureBoundaryEventAtDefault index rest

def layeredRelationFailureBoundaryToEventFlow :
    LayeredRelationFailureBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LayeredRelationFailureBoundaryUp.mk relation exactness failureBoundary weakening gate
      transport route provenance name =>
      [layeredRelationFailureBoundaryEncodeBHist relation,
        layeredRelationFailureBoundaryEncodeBHist exactness,
        layeredRelationFailureBoundaryEncodeBHist failureBoundary,
        layeredRelationFailureBoundaryEncodeBHist weakening,
        layeredRelationFailureBoundaryEncodeBHist gate,
        layeredRelationFailureBoundaryEncodeBHist transport,
        layeredRelationFailureBoundaryEncodeBHist route,
        layeredRelationFailureBoundaryEncodeBHist provenance,
        layeredRelationFailureBoundaryEncodeBHist name]

def layeredRelationFailureBoundaryFromEventFlow :
    EventFlow → Option LayeredRelationFailureBoundaryUp :=
  fun ef =>
    -- BEDC touchpoint anchor: BHist BMark
    some
      (LayeredRelationFailureBoundaryUp.mk
        (layeredRelationFailureBoundaryDecodeBHist
          (layeredRelationFailureBoundaryEventAtDefault 0 ef))
        (layeredRelationFailureBoundaryDecodeBHist
          (layeredRelationFailureBoundaryEventAtDefault 1 ef))
        (layeredRelationFailureBoundaryDecodeBHist
          (layeredRelationFailureBoundaryEventAtDefault 2 ef))
        (layeredRelationFailureBoundaryDecodeBHist
          (layeredRelationFailureBoundaryEventAtDefault 3 ef))
        (layeredRelationFailureBoundaryDecodeBHist
          (layeredRelationFailureBoundaryEventAtDefault 4 ef))
        (layeredRelationFailureBoundaryDecodeBHist
          (layeredRelationFailureBoundaryEventAtDefault 5 ef))
        (layeredRelationFailureBoundaryDecodeBHist
          (layeredRelationFailureBoundaryEventAtDefault 6 ef))
        (layeredRelationFailureBoundaryDecodeBHist
          (layeredRelationFailureBoundaryEventAtDefault 7 ef))
        (layeredRelationFailureBoundaryDecodeBHist
          (layeredRelationFailureBoundaryEventAtDefault 8 ef)))

private theorem layeredRelationFailureBoundary_round_trip :
    ∀ x : LayeredRelationFailureBoundaryUp,
      layeredRelationFailureBoundaryFromEventFlow
        (layeredRelationFailureBoundaryToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | LayeredRelationFailureBoundaryUp.mk relation exactness failureBoundary weakening gate transport route
      provenance name =>
      congrArg some
        (layeredRelationFailureBoundary_mk_congr
          (layeredRelationFailureBoundary_decode_encode_bhist relation)
          (layeredRelationFailureBoundary_decode_encode_bhist exactness)
          (layeredRelationFailureBoundary_decode_encode_bhist failureBoundary)
          (layeredRelationFailureBoundary_decode_encode_bhist weakening)
          (layeredRelationFailureBoundary_decode_encode_bhist gate)
          (layeredRelationFailureBoundary_decode_encode_bhist transport)
          (layeredRelationFailureBoundary_decode_encode_bhist route)
          (layeredRelationFailureBoundary_decode_encode_bhist provenance)
          (layeredRelationFailureBoundary_decode_encode_bhist name))

private theorem layeredRelationFailureBoundaryToEventFlow_injective
    {x y : LayeredRelationFailureBoundaryUp} :
    layeredRelationFailureBoundaryToEventFlow x =
      layeredRelationFailureBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      layeredRelationFailureBoundaryFromEventFlow
          (layeredRelationFailureBoundaryToEventFlow x) =
        layeredRelationFailureBoundaryFromEventFlow
          (layeredRelationFailureBoundaryToEventFlow y) :=
    congrArg layeredRelationFailureBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (layeredRelationFailureBoundary_round_trip x).symm
      (Eq.trans hread (layeredRelationFailureBoundary_round_trip y)))

def layeredRelationFailureBoundaryFields :
    LayeredRelationFailureBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LayeredRelationFailureBoundaryUp.mk relation exactness failureBoundary weakening gate
      transport route provenance name =>
      [relation, exactness, failureBoundary, weakening, gate, transport, route, provenance, name]

private theorem layeredRelationFailureBoundary_fields_faithful :
    ∀ x y : LayeredRelationFailureBoundaryUp,
      layeredRelationFailureBoundaryFields x =
        layeredRelationFailureBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk relation₁ exactness₁ failureBoundary₁ weakening₁ gate₁ transport₁ route₁ provenance₁
      name₁ =>
      cases y with
      | mk relation₂ exactness₂ failureBoundary₂ weakening₂ gate₂ transport₂ route₂
          provenance₂ name₂ =>
          injection hfields with hRelation tail0
          injection tail0 with hExactness tail1
          injection tail1 with hFailureBoundary tail2
          injection tail2 with hWeakening tail3
          injection tail3 with hGate tail4
          injection tail4 with hTransport tail5
          injection tail5 with hRoute tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hName _
          subst hRelation
          subst hExactness
          subst hFailureBoundary
          subst hWeakening
          subst hGate
          subst hTransport
          subst hRoute
          subst hProvenance
          subst hName
          rfl

instance layeredRelationFailureBoundaryBHistCarrier :
    BHistCarrier LayeredRelationFailureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := layeredRelationFailureBoundaryToEventFlow
  fromEventFlow := layeredRelationFailureBoundaryFromEventFlow

instance layeredRelationFailureBoundaryChapterTasteGate :
    ChapterTasteGate LayeredRelationFailureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      layeredRelationFailureBoundaryFromEventFlow
        (layeredRelationFailureBoundaryToEventFlow x) = some x
    exact layeredRelationFailureBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (layeredRelationFailureBoundaryToEventFlow_injective heq)

instance layeredRelationFailureBoundaryFieldFaithful :
    FieldFaithful LayeredRelationFailureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := layeredRelationFailureBoundaryFields
  field_faithful := layeredRelationFailureBoundary_fields_faithful

instance layeredRelationFailureBoundaryNontrivial :
    Nontrivial LayeredRelationFailureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LayeredRelationFailureBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LayeredRelationFailureBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LayeredRelationFailureBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  layeredRelationFailureBoundaryChapterTasteGate

theorem LayeredRelationFailureBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      layeredRelationFailureBoundaryDecodeBHist
        (layeredRelationFailureBoundaryEncodeBHist h) = h) ∧
      (∀ x : LayeredRelationFailureBoundaryUp,
        layeredRelationFailureBoundaryFromEventFlow
          (layeredRelationFailureBoundaryToEventFlow x) = some x) ∧
        (∀ x y : LayeredRelationFailureBoundaryUp,
          layeredRelationFailureBoundaryToEventFlow x =
            layeredRelationFailureBoundaryToEventFlow y → x = y) ∧
          layeredRelationFailureBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact And.intro layeredRelationFailureBoundary_decode_encode_bhist
    (And.intro layeredRelationFailureBoundary_round_trip
      (And.intro
        (by
          intro x y heq
          exact layeredRelationFailureBoundaryToEventFlow_injective heq)
        rfl))

theorem LayeredRelationFailureBoundary_failure_boundary_row_determinacy
    {relation exactness failureBoundary1 failureBoundary2 weakening gate transport route
      provenance name : BHist}
    (h :
      layeredRelationFailureBoundaryToEventFlow
          (LayeredRelationFailureBoundaryUp.mk relation exactness failureBoundary1 weakening
            gate transport route provenance name) =
        layeredRelationFailureBoundaryToEventFlow
          (LayeredRelationFailureBoundaryUp.mk relation exactness failureBoundary2 weakening
            gate transport route provenance name)) :
    failureBoundary1 = failureBoundary2 ∧
      LayeredRelationFailureBoundaryUp.mk relation exactness BHist.Empty weakening gate
          transport route provenance name ≠
        LayeredRelationFailureBoundaryUp.mk relation exactness (BHist.e0 BHist.Empty)
          weakening gate transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · have hmk :
        LayeredRelationFailureBoundaryUp.mk relation exactness failureBoundary1 weakening
            gate transport route provenance name =
          LayeredRelationFailureBoundaryUp.mk relation exactness failureBoundary2 weakening
            gate transport route provenance name :=
      layeredRelationFailureBoundaryToEventFlow_injective h
    cases hmk
    rfl
  · intro hrow
    cases hrow

end BEDC.Derived.LayeredRelationFailureBoundaryUp
