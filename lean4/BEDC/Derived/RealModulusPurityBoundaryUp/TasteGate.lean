import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealModulusPurityBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealModulusPurityBoundaryUp : Type where
  | mk
      (modulus bound purity witness refusal transport continuation provenance name : BHist) :
      RealModulusPurityBoundaryUp
  deriving DecidableEq

def realModulusPurityBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realModulusPurityBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realModulusPurityBoundaryEncodeBHist h

def realModulusPurityBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realModulusPurityBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realModulusPurityBoundaryDecodeBHist tail)

private theorem realModulusPurityBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      realModulusPurityBoundaryDecodeBHist (realModulusPurityBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realModulusPurityBoundaryFields : RealModulusPurityBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealModulusPurityBoundaryUp.mk modulus bound purity witness refusal transport
      continuation provenance name =>
      [modulus, bound, purity, witness, refusal, transport, continuation, provenance, name]

def realModulusPurityBoundaryToEventFlow : RealModulusPurityBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realModulusPurityBoundaryFields x).map realModulusPurityBoundaryEncodeBHist

def realModulusPurityBoundaryFromEventFlow :
    EventFlow → Option RealModulusPurityBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [modulus, bound, purity, witness, refusal, transport, continuation, provenance, name] =>
      some
        (RealModulusPurityBoundaryUp.mk
          (realModulusPurityBoundaryDecodeBHist modulus)
          (realModulusPurityBoundaryDecodeBHist bound)
          (realModulusPurityBoundaryDecodeBHist purity)
          (realModulusPurityBoundaryDecodeBHist witness)
          (realModulusPurityBoundaryDecodeBHist refusal)
          (realModulusPurityBoundaryDecodeBHist transport)
          (realModulusPurityBoundaryDecodeBHist continuation)
          (realModulusPurityBoundaryDecodeBHist provenance)
          (realModulusPurityBoundaryDecodeBHist name))
  | _ => none

private theorem realModulusPurityBoundary_round_trip :
    ∀ x : RealModulusPurityBoundaryUp,
      realModulusPurityBoundaryFromEventFlow
        (realModulusPurityBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk modulus bound purity witness refusal transport continuation provenance name =>
      change
        some
          (RealModulusPurityBoundaryUp.mk
            (realModulusPurityBoundaryDecodeBHist
              (realModulusPurityBoundaryEncodeBHist modulus))
            (realModulusPurityBoundaryDecodeBHist
              (realModulusPurityBoundaryEncodeBHist bound))
            (realModulusPurityBoundaryDecodeBHist
              (realModulusPurityBoundaryEncodeBHist purity))
            (realModulusPurityBoundaryDecodeBHist
              (realModulusPurityBoundaryEncodeBHist witness))
            (realModulusPurityBoundaryDecodeBHist
              (realModulusPurityBoundaryEncodeBHist refusal))
            (realModulusPurityBoundaryDecodeBHist
              (realModulusPurityBoundaryEncodeBHist transport))
            (realModulusPurityBoundaryDecodeBHist
              (realModulusPurityBoundaryEncodeBHist continuation))
            (realModulusPurityBoundaryDecodeBHist
              (realModulusPurityBoundaryEncodeBHist provenance))
            (realModulusPurityBoundaryDecodeBHist
              (realModulusPurityBoundaryEncodeBHist name))) =
          some
            (RealModulusPurityBoundaryUp.mk modulus bound purity witness refusal transport
              continuation provenance name)
      simp only [realModulusPurityBoundaryDecode_encode_bhist]

private theorem realModulusPurityBoundaryToEventFlow_injective
    {x y : RealModulusPurityBoundaryUp} :
    realModulusPurityBoundaryToEventFlow x =
        realModulusPurityBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realModulusPurityBoundaryFromEventFlow (realModulusPurityBoundaryToEventFlow x) =
        realModulusPurityBoundaryFromEventFlow (realModulusPurityBoundaryToEventFlow y) :=
    congrArg realModulusPurityBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realModulusPurityBoundary_round_trip x).symm
      (Eq.trans hread (realModulusPurityBoundary_round_trip y)))

private theorem realModulusPurityBoundary_field_faithful :
    ∀ x y : RealModulusPurityBoundaryUp,
      realModulusPurityBoundaryFields x = realModulusPurityBoundaryFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk modulus₁ bound₁ purity₁ witness₁ refusal₁ transport₁ continuation₁ provenance₁ name₁ =>
      cases y with
      | mk modulus₂ bound₂ purity₂ witness₂ refusal₂ transport₂ continuation₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance realModulusPurityBoundaryBHistCarrier :
    BHistCarrier RealModulusPurityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realModulusPurityBoundaryToEventFlow
  fromEventFlow := realModulusPurityBoundaryFromEventFlow

instance realModulusPurityBoundaryChapterTasteGate :
    ChapterTasteGate RealModulusPurityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realModulusPurityBoundaryFromEventFlow
        (realModulusPurityBoundaryToEventFlow x) = some x
    exact realModulusPurityBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realModulusPurityBoundaryToEventFlow_injective heq)

instance realModulusPurityBoundaryFieldFaithful :
    FieldFaithful RealModulusPurityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realModulusPurityBoundaryFields
  field_faithful := realModulusPurityBoundary_field_faithful

instance realModulusPurityBoundaryNontrivial : Nontrivial RealModulusPurityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealModulusPurityBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealModulusPurityBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealModulusPurityBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realModulusPurityBoundaryChapterTasteGate

end BEDC.Derived.RealModulusPurityBoundaryUp
