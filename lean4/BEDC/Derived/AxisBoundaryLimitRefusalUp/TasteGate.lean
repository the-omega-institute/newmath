import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# AxisBoundaryLimitRefusalUp TasteGate carrier.
-/

namespace BEDC.Derived.AxisBoundaryLimitRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisBoundaryLimitRefusalUp : Type where
  | mk :
      (boundary limitRefusal realRefusal completenessRefusal transport route provenance
        name : BHist) →
      AxisBoundaryLimitRefusalUp
  deriving DecidableEq

def axisBoundaryLimitRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisBoundaryLimitRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisBoundaryLimitRefusalEncodeBHist h

def axisBoundaryLimitRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisBoundaryLimitRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisBoundaryLimitRefusalDecodeBHist tail)

private theorem axisBoundaryLimitRefusalDecodeEncodeBHist :
    ∀ h : BHist,
      axisBoundaryLimitRefusalDecodeBHist
        (axisBoundaryLimitRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axisBoundaryLimitRefusalFields :
    AxisBoundaryLimitRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AxisBoundaryLimitRefusalUp.mk boundary limitRefusal realRefusal completenessRefusal
      transport route provenance name =>
      [boundary, limitRefusal, realRefusal, completenessRefusal, transport, route,
        provenance, name]

def axisBoundaryLimitRefusalToEventFlow :
    AxisBoundaryLimitRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (axisBoundaryLimitRefusalFields x).map axisBoundaryLimitRefusalEncodeBHist

def axisBoundaryLimitRefusalFromEventFlow :
    EventFlow → Option AxisBoundaryLimitRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | boundary :: rest0 =>
      match rest0 with
      | [] => none
      | limitRefusal :: rest1 =>
          match rest1 with
          | [] => none
          | realRefusal :: rest2 =>
              match rest2 with
              | [] => none
              | completenessRefusal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | name :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (AxisBoundaryLimitRefusalUp.mk
                                          (axisBoundaryLimitRefusalDecodeBHist boundary)
                                          (axisBoundaryLimitRefusalDecodeBHist limitRefusal)
                                          (axisBoundaryLimitRefusalDecodeBHist realRefusal)
                                          (axisBoundaryLimitRefusalDecodeBHist
                                            completenessRefusal)
                                          (axisBoundaryLimitRefusalDecodeBHist transport)
                                          (axisBoundaryLimitRefusalDecodeBHist route)
                                          (axisBoundaryLimitRefusalDecodeBHist provenance)
                                          (axisBoundaryLimitRefusalDecodeBHist name))
                                  | _ :: _ => none

private theorem axisBoundaryLimitRefusal_round_trip :
    ∀ x : AxisBoundaryLimitRefusalUp,
      axisBoundaryLimitRefusalFromEventFlow
        (axisBoundaryLimitRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk boundary limitRefusal realRefusal completenessRefusal transport route provenance name =>
      change
        some
          (AxisBoundaryLimitRefusalUp.mk
            (axisBoundaryLimitRefusalDecodeBHist
              (axisBoundaryLimitRefusalEncodeBHist boundary))
            (axisBoundaryLimitRefusalDecodeBHist
              (axisBoundaryLimitRefusalEncodeBHist limitRefusal))
            (axisBoundaryLimitRefusalDecodeBHist
              (axisBoundaryLimitRefusalEncodeBHist realRefusal))
            (axisBoundaryLimitRefusalDecodeBHist
              (axisBoundaryLimitRefusalEncodeBHist completenessRefusal))
            (axisBoundaryLimitRefusalDecodeBHist
              (axisBoundaryLimitRefusalEncodeBHist transport))
            (axisBoundaryLimitRefusalDecodeBHist
              (axisBoundaryLimitRefusalEncodeBHist route))
            (axisBoundaryLimitRefusalDecodeBHist
              (axisBoundaryLimitRefusalEncodeBHist provenance))
            (axisBoundaryLimitRefusalDecodeBHist
              (axisBoundaryLimitRefusalEncodeBHist name))) =
          some
            (AxisBoundaryLimitRefusalUp.mk boundary limitRefusal realRefusal
              completenessRefusal transport route provenance name)
      rw [axisBoundaryLimitRefusalDecodeEncodeBHist boundary,
        axisBoundaryLimitRefusalDecodeEncodeBHist limitRefusal,
        axisBoundaryLimitRefusalDecodeEncodeBHist realRefusal,
        axisBoundaryLimitRefusalDecodeEncodeBHist completenessRefusal,
        axisBoundaryLimitRefusalDecodeEncodeBHist transport,
        axisBoundaryLimitRefusalDecodeEncodeBHist route,
        axisBoundaryLimitRefusalDecodeEncodeBHist provenance,
        axisBoundaryLimitRefusalDecodeEncodeBHist name]

private theorem axisBoundaryLimitRefusalToEventFlow_injective
    {x y : AxisBoundaryLimitRefusalUp} :
    axisBoundaryLimitRefusalToEventFlow x =
      axisBoundaryLimitRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisBoundaryLimitRefusalFromEventFlow
          (axisBoundaryLimitRefusalToEventFlow x) =
        axisBoundaryLimitRefusalFromEventFlow
          (axisBoundaryLimitRefusalToEventFlow y) :=
    congrArg axisBoundaryLimitRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axisBoundaryLimitRefusal_round_trip x).symm
      (Eq.trans hread (axisBoundaryLimitRefusal_round_trip y)))

private theorem axisBoundaryLimitRefusal_fields_faithful :
    ∀ x y : AxisBoundaryLimitRefusalUp,
      axisBoundaryLimitRefusalFields x = axisBoundaryLimitRefusalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk boundary₁ limitRefusal₁ realRefusal₁ completenessRefusal₁ transport₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk boundary₂ limitRefusal₂ realRefusal₂ completenessRefusal₂ transport₂ route₂
          provenance₂ name₂ =>
          injection hfields with hboundary tail0
          injection tail0 with hlimitRefusal tail1
          injection tail1 with hrealRefusal tail2
          injection tail2 with hcompletenessRefusal tail3
          injection tail3 with htransport tail4
          injection tail4 with hroute tail5
          injection tail5 with hprovenance tail6
          injection tail6 with hname _
          subst hboundary
          subst hlimitRefusal
          subst hrealRefusal
          subst hcompletenessRefusal
          subst htransport
          subst hroute
          subst hprovenance
          subst hname
          rfl

instance axisBoundaryLimitRefusalBHistCarrier :
    BHistCarrier AxisBoundaryLimitRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisBoundaryLimitRefusalToEventFlow
  fromEventFlow := axisBoundaryLimitRefusalFromEventFlow

instance axisBoundaryLimitRefusalChapterTasteGate :
    ChapterTasteGate AxisBoundaryLimitRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axisBoundaryLimitRefusalFromEventFlow
      (axisBoundaryLimitRefusalToEventFlow x) = some x
    exact axisBoundaryLimitRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisBoundaryLimitRefusalToEventFlow_injective heq)

instance axisBoundaryLimitRefusalFieldFaithful :
    FieldFaithful AxisBoundaryLimitRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := axisBoundaryLimitRefusalFields
  field_faithful := axisBoundaryLimitRefusal_fields_faithful

instance axisBoundaryLimitRefusalNontrivial :
    Nontrivial AxisBoundaryLimitRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisBoundaryLimitRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxisBoundaryLimitRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxisBoundaryLimitRefusalUp :=
  axisBoundaryLimitRefusalChapterTasteGate

theorem AxisBoundaryLimitRefusalTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AxisBoundaryLimitRefusalUp) ∧
      Nonempty (FieldFaithful AxisBoundaryLimitRefusalUp) ∧
      Nonempty (Nontrivial AxisBoundaryLimitRefusalUp) ∧
        (∀ h : BHist,
          axisBoundaryLimitRefusalDecodeBHist
            (axisBoundaryLimitRefusalEncodeBHist h) = h) ∧
          axisBoundaryLimitRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨axisBoundaryLimitRefusalChapterTasteGate⟩,
      ⟨axisBoundaryLimitRefusalFieldFaithful⟩,
      ⟨axisBoundaryLimitRefusalNontrivial⟩,
      axisBoundaryLimitRefusalDecodeEncodeBHist, rfl⟩

end BEDC.Derived.AxisBoundaryLimitRefusalUp
