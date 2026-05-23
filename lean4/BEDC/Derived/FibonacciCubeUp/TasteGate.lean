import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FibonacciCubeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FibonacciCubeUp : Type where
  | mk :
      (length pathGraph word independentSet provenance dependencies packages nameCert :
        BHist) →
      FibonacciCubeUp
  deriving DecidableEq

def FibonacciCubeTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1]

def FibonacciCubeTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      FibonacciCubeTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      FibonacciCubeTasteGate_single_carrier_alignment_encodeBHist h

def FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem FibonacciCubeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist
          (FibonacciCubeTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def FibonacciCubeTasteGate_single_carrier_alignment_fields :
    FibonacciCubeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FibonacciCubeUp.mk length pathGraph word independentSet provenance dependencies packages
      nameCert =>
      [length, pathGraph, word, independentSet, provenance, dependencies, packages, nameCert]

def FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow :
    FibonacciCubeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      FibonacciCubeTasteGate_single_carrier_alignment_tag ::
        (FibonacciCubeTasteGate_single_carrier_alignment_fields x).map
          FibonacciCubeTasteGate_single_carrier_alignment_encodeBHist

def FibonacciCubeTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option FibonacciCubeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tag, length, pathGraph, word, independentSet, provenance, dependencies, packages,
      nameCert] =>
      match tag with
      | [BMark.b1, BMark.b0, BMark.b1] =>
          some
            (FibonacciCubeUp.mk
              (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist length)
              (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist pathGraph)
              (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist word)
              (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist independentSet)
              (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist provenance)
              (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist dependencies)
              (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist packages)
              (FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist nameCert))
      | _ => none
  | _ => none

private theorem FibonacciCubeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FibonacciCubeUp,
      FibonacciCubeTasteGate_single_carrier_alignment_fromEventFlow
          (FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk length pathGraph word independentSet provenance dependencies packages nameCert =>
      simp only [FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow,
        FibonacciCubeTasteGate_single_carrier_alignment_fields,
        FibonacciCubeTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, FibonacciCubeTasteGate_single_carrier_alignment_tag,
        FibonacciCubeTasteGate_single_carrier_alignment_decode_encode]

private theorem FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FibonacciCubeUp} :
    FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow x =
        FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FibonacciCubeTasteGate_single_carrier_alignment_fromEventFlow
          (FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow x) =
        FibonacciCubeTasteGate_single_carrier_alignment_fromEventFlow
          (FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg FibonacciCubeTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FibonacciCubeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FibonacciCubeTasteGate_single_carrier_alignment_round_trip y)))

private theorem FibonacciCubeTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : FibonacciCubeUp,
      FibonacciCubeTasteGate_single_carrier_alignment_fields x =
          FibonacciCubeTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk length₁ pathGraph₁ word₁ independentSet₁ provenance₁ dependencies₁ packages₁
      nameCert₁ =>
      cases y with
      | mk length₂ pathGraph₂ word₂ independentSet₂ provenance₂ dependencies₂ packages₂
          nameCert₂ =>
          injection hfields with hLength tail0
          injection tail0 with hPathGraph tail1
          injection tail1 with hWord tail2
          injection tail2 with hIndependentSet tail3
          injection tail3 with hProvenance tail4
          injection tail4 with hDependencies tail5
          injection tail5 with hPackages tail6
          injection tail6 with hNameCert _
          subst hLength
          subst hPathGraph
          subst hWord
          subst hIndependentSet
          subst hProvenance
          subst hDependencies
          subst hPackages
          subst hNameCert
          rfl

instance FibonacciCubeTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier FibonacciCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := FibonacciCubeTasteGate_single_carrier_alignment_fromEventFlow

instance FibonacciCubeTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate FibonacciCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FibonacciCubeTasteGate_single_carrier_alignment_fromEventFlow
          (FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact FibonacciCubeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance FibonacciCubeTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful FibonacciCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := FibonacciCubeTasteGate_single_carrier_alignment_fields
  field_faithful := FibonacciCubeTasteGate_single_carrier_alignment_field_faithful

instance FibonacciCubeTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial FibonacciCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FibonacciCubeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FibonacciCubeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def FibonacciCubeTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FibonacciCubeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FibonacciCubeTasteGate_single_carrier_alignment_ChapterTasteGate

theorem FibonacciCubeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        FibonacciCubeTasteGate_single_carrier_alignment_decodeBHist
            (FibonacciCubeTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      FibonacciCubeTasteGate_single_carrier_alignment_toEventFlow
          (FibonacciCubeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b1, BMark.b0, BMark.b1], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact FibonacciCubeTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.FibonacciCubeUp
