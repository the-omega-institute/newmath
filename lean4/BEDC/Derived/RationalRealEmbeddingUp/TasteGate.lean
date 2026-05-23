import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalRealEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalRealEmbeddingUp : Type where
  | mk
      (source streamWindow regularReadback dyadicTolerance realSeal transport replay
        provenance name : BHist) :
      RationalRealEmbeddingUp
  deriving DecidableEq

def RationalRealEmbeddingTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      RationalRealEmbeddingTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      RationalRealEmbeddingTasteGate_single_carrier_alignment_encodeBHist h

def RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RationalRealEmbeddingTasteGate_single_carrier_alignment_fields :
    RationalRealEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalRealEmbeddingUp.mk source streamWindow regularReadback dyadicTolerance
      realSeal transport replay provenance name =>
      [source, streamWindow, regularReadback, dyadicTolerance, realSeal, transport, replay,
        provenance, name]

def RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow :
    RationalRealEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RationalRealEmbeddingTasteGate_single_carrier_alignment_fields x).map
      RationalRealEmbeddingTasteGate_single_carrier_alignment_encodeBHist

def RationalRealEmbeddingTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RationalRealEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | source :: streamWindow :: regularReadback :: dyadicTolerance :: realSeal :: transport ::
      replay :: provenance :: name :: [] =>
      some
        (RationalRealEmbeddingUp.mk
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist source)
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist streamWindow)
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist regularReadback)
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist dyadicTolerance)
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist realSeal)
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist transport)
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist replay)
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist provenance)
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist name))
  | _ => none

private theorem RationalRealEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RationalRealEmbeddingUp,
      RationalRealEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk source streamWindow regularReadback dyadicTolerance realSeal transport replay provenance
      name =>
      simp only [RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow,
        RationalRealEmbeddingTasteGate_single_carrier_alignment_fields,
        RationalRealEmbeddingTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode]

private theorem RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalRealEmbeddingUp} :
    RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow x =
        RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          RationalRealEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) :=
        (RationalRealEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          RationalRealEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg RationalRealEmbeddingTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := RationalRealEmbeddingTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem RationalRealEmbeddingTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RationalRealEmbeddingUp,
      RationalRealEmbeddingTasteGate_single_carrier_alignment_fields x =
          RationalRealEmbeddingTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ streamWindow₁ regularReadback₁ dyadicTolerance₁ realSeal₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk source₂ streamWindow₂ regularReadback₂ dyadicTolerance₂ realSeal₂ transport₂ replay₂
          provenance₂ name₂ =>
          cases hfields
          rfl

instance RationalRealEmbeddingTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RationalRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RationalRealEmbeddingTasteGate_single_carrier_alignment_fromEventFlow

instance RationalRealEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RationalRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RationalRealEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RationalRealEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance RationalRealEmbeddingTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful RationalRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RationalRealEmbeddingTasteGate_single_carrier_alignment_fields
  field_faithful := RationalRealEmbeddingTasteGate_single_carrier_alignment_field_faithful

instance RationalRealEmbeddingTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial RationalRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalRealEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RationalRealEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RationalRealEmbeddingTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RationalRealEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RationalRealEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate

theorem RationalRealEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      RationalRealEmbeddingTasteGate_single_carrier_alignment_decodeBHist
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      RationalRealEmbeddingTasteGate_single_carrier_alignment_fields
          (RationalRealEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.RationalRealEmbeddingUp
