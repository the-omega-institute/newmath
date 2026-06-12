import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ForceMetaCICSameSchemaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ForceMetaCICSameSchemaUp : Type where
  | mk (A B L P Q R V H C K N : BHist) : ForceMetaCICSameSchemaUp
  deriving DecidableEq

def forceMetaCICSameSchemaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: forceMetaCICSameSchemaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: forceMetaCICSameSchemaEncodeBHist h

def forceMetaCICSameSchemaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (forceMetaCICSameSchemaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (forceMetaCICSameSchemaDecodeBHist tail)

private def forceMetaCICSameSchemaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => forceMetaCICSameSchemaEventAt index rest

private theorem forceMetaCICSameSchemaDecode_encode_bhist :
    ∀ h : BHist,
      forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def forceMetaCICSameSchemaFields :
    ForceMetaCICSameSchemaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ForceMetaCICSameSchemaUp.mk A B L P Q R V H C K N =>
      [A, B, L, P, Q, R, V, H, C, K, N]

def forceMetaCICSameSchemaToEventFlow :
    ForceMetaCICSameSchemaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ForceMetaCICSameSchemaUp.mk A B L P Q R V H C K N =>
      [forceMetaCICSameSchemaEncodeBHist A,
        forceMetaCICSameSchemaEncodeBHist B,
        forceMetaCICSameSchemaEncodeBHist L,
        forceMetaCICSameSchemaEncodeBHist P,
        forceMetaCICSameSchemaEncodeBHist Q,
        forceMetaCICSameSchemaEncodeBHist R,
        forceMetaCICSameSchemaEncodeBHist V,
        forceMetaCICSameSchemaEncodeBHist H,
        forceMetaCICSameSchemaEncodeBHist C,
        forceMetaCICSameSchemaEncodeBHist K,
        forceMetaCICSameSchemaEncodeBHist N]

def forceMetaCICSameSchemaFromEventFlow :
    EventFlow → Option ForceMetaCICSameSchemaUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ForceMetaCICSameSchemaUp.mk
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 0 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 1 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 2 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 3 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 4 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 5 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 6 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 7 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 8 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 9 ef))
          (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEventAt 10 ef)))

private theorem forceMetaCICSameSchema_round_trip :
    ∀ x : ForceMetaCICSameSchemaUp,
      forceMetaCICSameSchemaFromEventFlow
          (forceMetaCICSameSchemaToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B L P Q R V H C K N =>
      change
        some
          (ForceMetaCICSameSchemaUp.mk
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist A))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist B))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist L))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist P))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist Q))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist R))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist V))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist H))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist C))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist K))
            (forceMetaCICSameSchemaDecodeBHist (forceMetaCICSameSchemaEncodeBHist N))) =
          some (ForceMetaCICSameSchemaUp.mk A B L P Q R V H C K N)
      rw [forceMetaCICSameSchemaDecode_encode_bhist A,
        forceMetaCICSameSchemaDecode_encode_bhist B,
        forceMetaCICSameSchemaDecode_encode_bhist L,
        forceMetaCICSameSchemaDecode_encode_bhist P,
        forceMetaCICSameSchemaDecode_encode_bhist Q,
        forceMetaCICSameSchemaDecode_encode_bhist R,
        forceMetaCICSameSchemaDecode_encode_bhist V,
        forceMetaCICSameSchemaDecode_encode_bhist H,
        forceMetaCICSameSchemaDecode_encode_bhist C,
        forceMetaCICSameSchemaDecode_encode_bhist K,
        forceMetaCICSameSchemaDecode_encode_bhist N]

private theorem forceMetaCICSameSchemaToEventFlow_injective
    {x y : ForceMetaCICSameSchemaUp} :
    forceMetaCICSameSchemaToEventFlow x =
        forceMetaCICSameSchemaToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      forceMetaCICSameSchemaFromEventFlow
          (forceMetaCICSameSchemaToEventFlow x) =
        forceMetaCICSameSchemaFromEventFlow
          (forceMetaCICSameSchemaToEventFlow y) :=
    congrArg forceMetaCICSameSchemaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (forceMetaCICSameSchema_round_trip x).symm
      (Eq.trans hread (forceMetaCICSameSchema_round_trip y)))

private theorem forceMetaCICSameSchemaFields_faithful :
    ∀ x y : ForceMetaCICSameSchemaUp,
      forceMetaCICSameSchemaFields x = forceMetaCICSameSchemaFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ L₁ P₁ Q₁ R₁ V₁ H₁ C₁ K₁ N₁ =>
      cases y with
      | mk A₂ B₂ L₂ P₂ Q₂ R₂ V₂ H₂ C₂ K₂ N₂ =>
          cases hfields
          rfl

instance forceMetaCICSameSchemaBHistCarrier :
    BHistCarrier ForceMetaCICSameSchemaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := forceMetaCICSameSchemaToEventFlow
  fromEventFlow := forceMetaCICSameSchemaFromEventFlow

instance forceMetaCICSameSchemaChapterTasteGate :
    ChapterTasteGate ForceMetaCICSameSchemaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      forceMetaCICSameSchemaFromEventFlow
          (forceMetaCICSameSchemaToEventFlow x) =
        some x
    exact forceMetaCICSameSchema_round_trip x
  layer_separation := by
    intro x y hxy heq
    change
      forceMetaCICSameSchemaToEventFlow x =
        forceMetaCICSameSchemaToEventFlow y at heq
    exact hxy (forceMetaCICSameSchemaToEventFlow_injective heq)

instance forceMetaCICSameSchemaFieldFaithful :
    FieldFaithful ForceMetaCICSameSchemaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := forceMetaCICSameSchemaFields
  field_faithful := forceMetaCICSameSchemaFields_faithful

instance forceMetaCICSameSchemaNontrivial :
    Nontrivial ForceMetaCICSameSchemaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ForceMetaCICSameSchemaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ForceMetaCICSameSchemaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ForceMetaCICSameSchemaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  forceMetaCICSameSchemaChapterTasteGate

theorem ForceMetaCICSameSchemaTasteGate_single_carrier_alignment :
    (∀ h : BHist, forceMetaCICSameSchemaDecodeBHist
        (forceMetaCICSameSchemaEncodeBHist h) = h) ∧
      (∀ x : ForceMetaCICSameSchemaUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        Nonempty (ChapterTasteGate ForceMetaCICSameSchemaUp) ∧
          forceMetaCICSameSchemaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact forceMetaCICSameSchemaDecode_encode_bhist
  · constructor
    · intro x
      change
        forceMetaCICSameSchemaFromEventFlow
            (forceMetaCICSameSchemaToEventFlow x) =
          some x
      exact forceMetaCICSameSchema_round_trip x
    · constructor
      · exact ⟨forceMetaCICSameSchemaChapterTasteGate⟩
      · rfl

end BEDC.Derived.ForceMetaCICSameSchemaUp
