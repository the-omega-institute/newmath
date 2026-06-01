import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicDensityRealEmbeddingComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicDensityRealEmbeddingComparisonUp : Type where
  | mk (density embedding comparison stream readback realSeal transport continuation provenance
      name : BHist) : DyadicDensityRealEmbeddingComparisonUp
  deriving DecidableEq

def dyadicDensityRealEmbeddingComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicDensityRealEmbeddingComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicDensityRealEmbeddingComparisonEncodeBHist h

def dyadicDensityRealEmbeddingComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicDensityRealEmbeddingComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicDensityRealEmbeddingComparisonDecodeBHist tail)

private theorem dyadicDensityRealEmbeddingComparison_decode_encode :
    ∀ h : BHist,
      dyadicDensityRealEmbeddingComparisonDecodeBHist
          (dyadicDensityRealEmbeddingComparisonEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicDensityRealEmbeddingComparisonFields :
    DyadicDensityRealEmbeddingComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicDensityRealEmbeddingComparisonUp.mk density embedding comparison stream readback
      realSeal transport continuation provenance name =>
      [density, embedding, comparison, stream, readback, realSeal, transport, continuation,
        provenance, name]

def dyadicDensityRealEmbeddingComparisonToEventFlow :
    DyadicDensityRealEmbeddingComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map dyadicDensityRealEmbeddingComparisonEncodeBHist
        (dyadicDensityRealEmbeddingComparisonFields x)

def dyadicDensityRealEmbeddingComparisonFromEventFlow :
    EventFlow → Option DyadicDensityRealEmbeddingComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | density :: embedding :: comparison :: stream :: readback :: realSeal :: transport ::
      continuation :: provenance :: name :: [] =>
      some
        (DyadicDensityRealEmbeddingComparisonUp.mk
          (dyadicDensityRealEmbeddingComparisonDecodeBHist density)
          (dyadicDensityRealEmbeddingComparisonDecodeBHist embedding)
          (dyadicDensityRealEmbeddingComparisonDecodeBHist comparison)
          (dyadicDensityRealEmbeddingComparisonDecodeBHist stream)
          (dyadicDensityRealEmbeddingComparisonDecodeBHist readback)
          (dyadicDensityRealEmbeddingComparisonDecodeBHist realSeal)
          (dyadicDensityRealEmbeddingComparisonDecodeBHist transport)
          (dyadicDensityRealEmbeddingComparisonDecodeBHist continuation)
          (dyadicDensityRealEmbeddingComparisonDecodeBHist provenance)
          (dyadicDensityRealEmbeddingComparisonDecodeBHist name))
  | _ => none

private theorem dyadicDensityRealEmbeddingComparison_round_trip :
    ∀ x : DyadicDensityRealEmbeddingComparisonUp,
      dyadicDensityRealEmbeddingComparisonFromEventFlow
          (dyadicDensityRealEmbeddingComparisonToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk density embedding comparison stream readback realSeal transport continuation provenance
      name =>
      simp only [dyadicDensityRealEmbeddingComparisonToEventFlow,
        dyadicDensityRealEmbeddingComparisonFields,
        dyadicDensityRealEmbeddingComparisonFromEventFlow, List.map_cons, List.map_nil,
        dyadicDensityRealEmbeddingComparison_decode_encode]

private theorem dyadicDensityRealEmbeddingComparisonToEventFlow_injective
    {x y : DyadicDensityRealEmbeddingComparisonUp} :
    dyadicDensityRealEmbeddingComparisonToEventFlow x =
        dyadicDensityRealEmbeddingComparisonToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicDensityRealEmbeddingComparisonFromEventFlow
          (dyadicDensityRealEmbeddingComparisonToEventFlow x) =
        dyadicDensityRealEmbeddingComparisonFromEventFlow
          (dyadicDensityRealEmbeddingComparisonToEventFlow y) :=
    congrArg dyadicDensityRealEmbeddingComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicDensityRealEmbeddingComparison_round_trip x).symm
      (Eq.trans hread (dyadicDensityRealEmbeddingComparison_round_trip y)))

private theorem dyadicDensityRealEmbeddingComparison_fields_faithful :
    ∀ x y : DyadicDensityRealEmbeddingComparisonUp,
      dyadicDensityRealEmbeddingComparisonFields x =
          dyadicDensityRealEmbeddingComparisonFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk density₁ embedding₁ comparison₁ stream₁ readback₁ realSeal₁ transport₁ continuation₁
      provenance₁ name₁ =>
      cases y with
      | mk density₂ embedding₂ comparison₂ stream₂ readback₂ realSeal₂ transport₂ continuation₂
          provenance₂ name₂ =>
          cases hfields
          rfl

instance dyadicDensityRealEmbeddingComparisonBHistCarrier :
    BHistCarrier DyadicDensityRealEmbeddingComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicDensityRealEmbeddingComparisonToEventFlow
  fromEventFlow := dyadicDensityRealEmbeddingComparisonFromEventFlow

instance dyadicDensityRealEmbeddingComparisonChapterTasteGate :
    ChapterTasteGate DyadicDensityRealEmbeddingComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicDensityRealEmbeddingComparisonFromEventFlow
          (dyadicDensityRealEmbeddingComparisonToEventFlow x) =
        some x
    exact dyadicDensityRealEmbeddingComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicDensityRealEmbeddingComparisonToEventFlow_injective heq)

instance dyadicDensityRealEmbeddingComparisonFieldFaithful :
    FieldFaithful DyadicDensityRealEmbeddingComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicDensityRealEmbeddingComparisonFields
  field_faithful := dyadicDensityRealEmbeddingComparison_fields_faithful

def taste_gate : ChapterTasteGate DyadicDensityRealEmbeddingComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicDensityRealEmbeddingComparisonChapterTasteGate

theorem DyadicDensityRealEmbeddingComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicDensityRealEmbeddingComparisonDecodeBHist
          (dyadicDensityRealEmbeddingComparisonEncodeBHist h) =
        h) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

end BEDC.Derived.DyadicDensityRealEmbeddingComparisonUp
