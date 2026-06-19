import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionEmbeddingReflectionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionEmbeddingReflectionUp : Type where
  | mk (A G K R S D Q E H C P N : BHist) : CauchyCompletionEmbeddingReflectionUp
  deriving DecidableEq

def cauchyCompletionEmbeddingReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionEmbeddingReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionEmbeddingReflectionEncodeBHist h

def cauchyCompletionEmbeddingReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionEmbeddingReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionEmbeddingReflectionDecodeBHist tail)

private theorem cauchyCompletionEmbeddingReflection_decode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionEmbeddingReflectionDecodeBHist
          (cauchyCompletionEmbeddingReflectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionEmbeddingReflectionFields :
    CauchyCompletionEmbeddingReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionEmbeddingReflectionUp.mk A G K R S D Q E H C P N =>
      [A, G, K, R, S, D, Q, E, H, C, P, N]

def cauchyCompletionEmbeddingReflectionToEventFlow :
    CauchyCompletionEmbeddingReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletionEmbeddingReflectionFields x).map
        cauchyCompletionEmbeddingReflectionEncodeBHist

private def cauchyCompletionEmbeddingReflectionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionEmbeddingReflectionRawAt index rest

def cauchyCompletionEmbeddingReflectionFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionEmbeddingReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionEmbeddingReflectionUp.mk
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 0 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 1 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 2 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 3 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 4 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 5 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 6 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 7 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 8 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 9 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 10 ef))
      (cauchyCompletionEmbeddingReflectionDecodeBHist
        (cauchyCompletionEmbeddingReflectionRawAt 11 ef)))

private theorem cauchyCompletionEmbeddingReflection_round_trip
    (x : CauchyCompletionEmbeddingReflectionUp) :
    cauchyCompletionEmbeddingReflectionFromEventFlow
        (cauchyCompletionEmbeddingReflectionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A G K R S D Q E H C P N =>
      change
        some
          (CauchyCompletionEmbeddingReflectionUp.mk
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist A))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist G))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist K))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist R))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist S))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist D))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist Q))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist E))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist H))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist C))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist P))
            (cauchyCompletionEmbeddingReflectionDecodeBHist
              (cauchyCompletionEmbeddingReflectionEncodeBHist N))) =
          some (CauchyCompletionEmbeddingReflectionUp.mk A G K R S D Q E H C P N)
      rw [cauchyCompletionEmbeddingReflection_decode_encode_bhist A,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist G,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist K,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist R,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist S,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist D,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist Q,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist E,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist H,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist C,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist P,
        cauchyCompletionEmbeddingReflection_decode_encode_bhist N]

private theorem cauchyCompletionEmbeddingReflectionToEventFlow_injective
    {x y : CauchyCompletionEmbeddingReflectionUp} :
    cauchyCompletionEmbeddingReflectionToEventFlow x =
        cauchyCompletionEmbeddingReflectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionEmbeddingReflectionFromEventFlow
          (cauchyCompletionEmbeddingReflectionToEventFlow x) =
        cauchyCompletionEmbeddingReflectionFromEventFlow
          (cauchyCompletionEmbeddingReflectionToEventFlow y) :=
    congrArg cauchyCompletionEmbeddingReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionEmbeddingReflection_round_trip x).symm
      (Eq.trans hread (cauchyCompletionEmbeddingReflection_round_trip y)))

private theorem cauchyCompletionEmbeddingReflection_field_faithful
    (x y : CauchyCompletionEmbeddingReflectionUp) :
    cauchyCompletionEmbeddingReflectionFields x =
        cauchyCompletionEmbeddingReflectionFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  cases x with
  | mk A₁ G₁ K₁ R₁ S₁ D₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ G₂ K₂ R₂ S₂ D₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyCompletionEmbeddingReflectionBHistCarrier :
    BHistCarrier CauchyCompletionEmbeddingReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionEmbeddingReflectionToEventFlow
  fromEventFlow := cauchyCompletionEmbeddingReflectionFromEventFlow

instance cauchyCompletionEmbeddingReflectionChapterTasteGate :
    ChapterTasteGate CauchyCompletionEmbeddingReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionEmbeddingReflectionFromEventFlow
          (cauchyCompletionEmbeddingReflectionToEventFlow x) =
        some x
    exact cauchyCompletionEmbeddingReflection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionEmbeddingReflectionToEventFlow_injective heq)

instance cauchyCompletionEmbeddingReflectionFieldFaithful :
    FieldFaithful CauchyCompletionEmbeddingReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionEmbeddingReflectionFields
  field_faithful := cauchyCompletionEmbeddingReflection_field_faithful

instance cauchyCompletionEmbeddingReflectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyCompletionEmbeddingReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionEmbeddingReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CauchyCompletionEmbeddingReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionEmbeddingReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionEmbeddingReflectionChapterTasteGate

theorem CauchyCompletionEmbeddingReflectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletionEmbeddingReflectionUp) ∧
      Nonempty (FieldFaithful CauchyCompletionEmbeddingReflectionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyCompletionEmbeddingReflectionUp) ∧
          (∀ h : BHist,
            cauchyCompletionEmbeddingReflectionDecodeBHist
                (cauchyCompletionEmbeddingReflectionEncodeBHist h) =
              h) ∧
            (∀ x : CauchyCompletionEmbeddingReflectionUp,
              cauchyCompletionEmbeddingReflectionFromEventFlow
                  (cauchyCompletionEmbeddingReflectionToEventFlow x) =
                some x) ∧
              cauchyCompletionEmbeddingReflectionEncodeBHist BHist.Empty =
                ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨Nonempty.intro cauchyCompletionEmbeddingReflectionChapterTasteGate,
      Nonempty.intro cauchyCompletionEmbeddingReflectionFieldFaithful,
      Nonempty.intro cauchyCompletionEmbeddingReflectionNontrivial,
      cauchyCompletionEmbeddingReflection_decode_encode_bhist,
      cauchyCompletionEmbeddingReflection_round_trip,
      rfl⟩

end BEDC.Derived.CauchyCompletionEmbeddingReflectionUp.TasteGate
