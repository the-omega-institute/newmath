import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WhitneyEmbeddingFiniteAtlasUp : Type where
  | mk (M K A F V S E H C P N : BHist) : WhitneyEmbeddingFiniteAtlasUp
  deriving DecidableEq

def whitneyEmbeddingFiniteAtlasEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: whitneyEmbeddingFiniteAtlasEncodeBHist h
  | BHist.e1 h => BMark.b1 :: whitneyEmbeddingFiniteAtlasEncodeBHist h

def whitneyEmbeddingFiniteAtlasDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (whitneyEmbeddingFiniteAtlasDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (whitneyEmbeddingFiniteAtlasDecodeBHist tail)

private theorem whitneyEmbeddingFiniteAtlas_decode_encode_bhist :
    ∀ h : BHist,
      whitneyEmbeddingFiniteAtlasDecodeBHist
          (whitneyEmbeddingFiniteAtlasEncodeBHist h) =
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

def whitneyEmbeddingFiniteAtlasToEventFlow : WhitneyEmbeddingFiniteAtlasUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WhitneyEmbeddingFiniteAtlasUp.mk M K A F V S E H C P N =>
      [whitneyEmbeddingFiniteAtlasEncodeBHist M,
        whitneyEmbeddingFiniteAtlasEncodeBHist K,
        whitneyEmbeddingFiniteAtlasEncodeBHist A,
        whitneyEmbeddingFiniteAtlasEncodeBHist F,
        whitneyEmbeddingFiniteAtlasEncodeBHist V,
        whitneyEmbeddingFiniteAtlasEncodeBHist S,
        whitneyEmbeddingFiniteAtlasEncodeBHist E,
        whitneyEmbeddingFiniteAtlasEncodeBHist H,
        whitneyEmbeddingFiniteAtlasEncodeBHist C,
        whitneyEmbeddingFiniteAtlasEncodeBHist P,
        whitneyEmbeddingFiniteAtlasEncodeBHist N]

private def whitneyEmbeddingFiniteAtlasEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      whitneyEmbeddingFiniteAtlasEventAtDefault index rest

def whitneyEmbeddingFiniteAtlasFromEventFlow
    (ef : EventFlow) : Option WhitneyEmbeddingFiniteAtlasUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WhitneyEmbeddingFiniteAtlasUp.mk
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 0 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 1 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 2 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 3 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 4 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 5 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 6 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 7 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 8 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 9 ef))
      (whitneyEmbeddingFiniteAtlasDecodeBHist
        (whitneyEmbeddingFiniteAtlasEventAtDefault 10 ef)))

private theorem whitneyEmbeddingFiniteAtlas_round_trip :
    ∀ x : WhitneyEmbeddingFiniteAtlasUp,
      whitneyEmbeddingFiniteAtlasFromEventFlow
          (whitneyEmbeddingFiniteAtlasToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K A F V S E H C P N =>
      change
        some
          (WhitneyEmbeddingFiniteAtlasUp.mk
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist M))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist K))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist A))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist F))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist V))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist S))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist E))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist H))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist C))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist P))
            (whitneyEmbeddingFiniteAtlasDecodeBHist
              (whitneyEmbeddingFiniteAtlasEncodeBHist N))) =
          some (WhitneyEmbeddingFiniteAtlasUp.mk M K A F V S E H C P N)
      rw [whitneyEmbeddingFiniteAtlas_decode_encode_bhist M,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist K,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist A,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist F,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist V,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist S,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist E,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist H,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist C,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist P,
        whitneyEmbeddingFiniteAtlas_decode_encode_bhist N]

private theorem whitneyEmbeddingFiniteAtlasToEventFlow_injective
    {x y : WhitneyEmbeddingFiniteAtlasUp} :
    whitneyEmbeddingFiniteAtlasToEventFlow x =
        whitneyEmbeddingFiniteAtlasToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      whitneyEmbeddingFiniteAtlasFromEventFlow
          (whitneyEmbeddingFiniteAtlasToEventFlow x) =
        whitneyEmbeddingFiniteAtlasFromEventFlow
          (whitneyEmbeddingFiniteAtlasToEventFlow y) :=
    congrArg whitneyEmbeddingFiniteAtlasFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (whitneyEmbeddingFiniteAtlas_round_trip x).symm
      (Eq.trans hread (whitneyEmbeddingFiniteAtlas_round_trip y)))

private def whitneyEmbeddingFiniteAtlasFields :
    WhitneyEmbeddingFiniteAtlasUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WhitneyEmbeddingFiniteAtlasUp.mk M K A F V S E H C P N =>
      [M, K, A, F, V, S, E, H, C, P, N]

private theorem whitneyEmbeddingFiniteAtlas_fields_faithful :
    ∀ x y : WhitneyEmbeddingFiniteAtlasUp,
      whitneyEmbeddingFiniteAtlasFields x = whitneyEmbeddingFiniteAtlasFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk M₁ K₁ A₁ F₁ V₁ S₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ K₂ A₂ F₂ V₂ S₂ E₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance whitneyEmbeddingFiniteAtlasBHistCarrier :
    BHistCarrier WhitneyEmbeddingFiniteAtlasUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := whitneyEmbeddingFiniteAtlasToEventFlow
  fromEventFlow := whitneyEmbeddingFiniteAtlasFromEventFlow

instance whitneyEmbeddingFiniteAtlasChapterTasteGate :
    ChapterTasteGate WhitneyEmbeddingFiniteAtlasUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      whitneyEmbeddingFiniteAtlasFromEventFlow
          (whitneyEmbeddingFiniteAtlasToEventFlow x) =
        some x
    exact whitneyEmbeddingFiniteAtlas_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (whitneyEmbeddingFiniteAtlasToEventFlow_injective heq)

instance whitneyEmbeddingFiniteAtlasFieldFaithful :
    FieldFaithful WhitneyEmbeddingFiniteAtlasUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := whitneyEmbeddingFiniteAtlasFields
  field_faithful := whitneyEmbeddingFiniteAtlas_fields_faithful

instance whitneyEmbeddingFiniteAtlasNontrivial :
    BEDC.Meta.TasteGate.Nontrivial WhitneyEmbeddingFiniteAtlasUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WhitneyEmbeddingFiniteAtlasUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WhitneyEmbeddingFiniteAtlasUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hM _ _ _ _ _ _ _ _ _ _
        cases hM⟩

theorem WhitneyEmbeddingFiniteAtlasTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      whitneyEmbeddingFiniteAtlasDecodeBHist
          (whitneyEmbeddingFiniteAtlasEncodeBHist h) =
        h) ∧
      (∀ x : WhitneyEmbeddingFiniteAtlasUp,
        whitneyEmbeddingFiniteAtlasFromEventFlow
            (whitneyEmbeddingFiniteAtlasToEventFlow x) =
          some x) ∧
        (∀ x y : WhitneyEmbeddingFiniteAtlasUp,
          whitneyEmbeddingFiniteAtlasToEventFlow x =
              whitneyEmbeddingFiniteAtlasToEventFlow y ->
            x = y) ∧
          whitneyEmbeddingFiniteAtlasEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨whitneyEmbeddingFiniteAtlas_decode_encode_bhist,
      whitneyEmbeddingFiniteAtlas_round_trip,
      (fun _ _ heq => whitneyEmbeddingFiniteAtlasToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp
