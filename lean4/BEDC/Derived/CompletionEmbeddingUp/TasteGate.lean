import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionEmbeddingUp : Type where
  | mk
      (sourceMetric completionTarget denseImage isometry regularCauchy hausdorffBoundary
        realSeal transport replay provenance localCert : BHist) :
      CompletionEmbeddingUp
  deriving DecidableEq

def CompletionEmbeddingTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CompletionEmbeddingTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: CompletionEmbeddingTasteGate_single_carrier_alignment_encodeBHist h

def CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist
          (CompletionEmbeddingTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CompletionEmbeddingTasteGate_single_carrier_alignment_fields :
    CompletionEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionEmbeddingUp.mk sourceMetric completionTarget denseImage isometry regularCauchy
      hausdorffBoundary realSeal transport replay provenance localCert =>
      [sourceMetric, completionTarget, denseImage, isometry, regularCauchy,
        hausdorffBoundary, realSeal, transport, replay, provenance, localCert]

def CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow :
    CompletionEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CompletionEmbeddingTasteGate_single_carrier_alignment_fields x).map
      CompletionEmbeddingTasteGate_single_carrier_alignment_encodeBHist

def CompletionEmbeddingTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CompletionEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | sourceMetric :: completionTarget :: denseImage :: isometry :: regularCauchy ::
      hausdorffBoundary :: realSeal :: transport :: replay :: provenance :: localCert :: [] =>
      some
        (CompletionEmbeddingUp.mk
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist sourceMetric)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist completionTarget)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist denseImage)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist isometry)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist regularCauchy)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist hausdorffBoundary)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist realSeal)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist transport)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist replay)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist provenance)
          (CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist localCert))
  | _ => none

private theorem CompletionEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionEmbeddingUp,
      CompletionEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk sourceMetric completionTarget denseImage isometry regularCauchy hausdorffBoundary
      realSeal transport replay provenance localCert =>
      simp only [CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow,
        CompletionEmbeddingTasteGate_single_carrier_alignment_fields,
        CompletionEmbeddingTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, CompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode]

private theorem CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionEmbeddingUp} :
    CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow x =
        CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          CompletionEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
            (CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) :=
        (CompletionEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CompletionEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
            (CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg CompletionEmbeddingTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := CompletionEmbeddingTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem CompletionEmbeddingTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CompletionEmbeddingUp,
      CompletionEmbeddingTasteGate_single_carrier_alignment_fields x =
          CompletionEmbeddingTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sourceMetric₁ completionTarget₁ denseImage₁ isometry₁ regularCauchy₁
      hausdorffBoundary₁ realSeal₁ transport₁ replay₁ provenance₁ localCert₁ =>
      cases y with
      | mk sourceMetric₂ completionTarget₂ denseImage₂ isometry₂ regularCauchy₂
          hausdorffBoundary₂ realSeal₂ transport₂ replay₂ provenance₂ localCert₂ =>
          cases hfields
          rfl

instance CompletionEmbeddingTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CompletionEmbeddingTasteGate_single_carrier_alignment_fromEventFlow

instance CompletionEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CompletionEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CompletionEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CompletionEmbeddingTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CompletionEmbeddingTasteGate_single_carrier_alignment_fields
  field_faithful := CompletionEmbeddingTasteGate_single_carrier_alignment_field_faithful

instance CompletionEmbeddingTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial CompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompletionEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CompletionEmbeddingTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CompletionEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CompletionEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate

theorem CompletionEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CompletionEmbeddingTasteGate_single_carrier_alignment_decodeBHist
          (CompletionEmbeddingTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CompletionEmbeddingTasteGate_single_carrier_alignment_fields
          (CompletionEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨CompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CompletionEmbeddingUp
