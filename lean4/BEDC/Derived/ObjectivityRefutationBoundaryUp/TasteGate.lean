import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObjectivityRefutationBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObjectivityRefutationBoundaryUp : Type where
  | mk : (H K A W R T P N : BHist) → ObjectivityRefutationBoundaryUp
  deriving DecidableEq

def objectivityRefutationBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: objectivityRefutationBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: objectivityRefutationBoundaryEncodeBHist h

def objectivityRefutationBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (objectivityRefutationBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (objectivityRefutationBoundaryDecodeBHist tail)

private theorem objectivityRefutationBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      objectivityRefutationBoundaryDecodeBHist
        (objectivityRefutationBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def objectivityRefutationBoundaryFields :
    ObjectivityRefutationBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObjectivityRefutationBoundaryUp.mk H K A W R T P N => [H, K, A, W, R, T, P, N]

def objectivityRefutationBoundaryToEventFlow :
    ObjectivityRefutationBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (objectivityRefutationBoundaryFields x).map
      objectivityRefutationBoundaryEncodeBHist

private def objectivityRefutationBoundaryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      objectivityRefutationBoundaryEventAtDefault index rest

def objectivityRefutationBoundaryFromEventFlow :
    EventFlow → Option ObjectivityRefutationBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ObjectivityRefutationBoundaryUp.mk
          (objectivityRefutationBoundaryDecodeBHist
            (objectivityRefutationBoundaryEventAtDefault 0 ef))
          (objectivityRefutationBoundaryDecodeBHist
            (objectivityRefutationBoundaryEventAtDefault 1 ef))
          (objectivityRefutationBoundaryDecodeBHist
            (objectivityRefutationBoundaryEventAtDefault 2 ef))
          (objectivityRefutationBoundaryDecodeBHist
            (objectivityRefutationBoundaryEventAtDefault 3 ef))
          (objectivityRefutationBoundaryDecodeBHist
            (objectivityRefutationBoundaryEventAtDefault 4 ef))
          (objectivityRefutationBoundaryDecodeBHist
            (objectivityRefutationBoundaryEventAtDefault 5 ef))
          (objectivityRefutationBoundaryDecodeBHist
            (objectivityRefutationBoundaryEventAtDefault 6 ef))
          (objectivityRefutationBoundaryDecodeBHist
            (objectivityRefutationBoundaryEventAtDefault 7 ef)))

private theorem objectivityRefutationBoundary_round_trip :
    ∀ x : ObjectivityRefutationBoundaryUp,
      objectivityRefutationBoundaryFromEventFlow
        (objectivityRefutationBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H K A W R T P N =>
      change
        some
          (ObjectivityRefutationBoundaryUp.mk
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist H))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist K))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist A))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist W))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist R))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist T))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist P))
            (objectivityRefutationBoundaryDecodeBHist
              (objectivityRefutationBoundaryEncodeBHist N))) =
          some (ObjectivityRefutationBoundaryUp.mk H K A W R T P N)
      rw [objectivityRefutationBoundaryDecode_encode_bhist H,
        objectivityRefutationBoundaryDecode_encode_bhist K,
        objectivityRefutationBoundaryDecode_encode_bhist A,
        objectivityRefutationBoundaryDecode_encode_bhist W,
        objectivityRefutationBoundaryDecode_encode_bhist R,
        objectivityRefutationBoundaryDecode_encode_bhist T,
        objectivityRefutationBoundaryDecode_encode_bhist P,
        objectivityRefutationBoundaryDecode_encode_bhist N]

private theorem objectivityRefutationBoundaryToEventFlow_injective
    {x y : ObjectivityRefutationBoundaryUp} :
    objectivityRefutationBoundaryToEventFlow x =
      objectivityRefutationBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      objectivityRefutationBoundaryFromEventFlow
          (objectivityRefutationBoundaryToEventFlow x) =
        objectivityRefutationBoundaryFromEventFlow
          (objectivityRefutationBoundaryToEventFlow y) :=
    congrArg objectivityRefutationBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (objectivityRefutationBoundary_round_trip x).symm
      (Eq.trans hread (objectivityRefutationBoundary_round_trip y)))

private theorem objectivityRefutationBoundary_fields_faithful :
    ∀ x y : ObjectivityRefutationBoundaryUp,
      objectivityRefutationBoundaryFields x =
        objectivityRefutationBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ K₁ A₁ W₁ R₁ T₁ P₁ N₁ =>
      cases y with
      | mk H₂ K₂ A₂ W₂ R₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance objectivityRefutationBoundaryBHistCarrier :
    BHistCarrier ObjectivityRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := objectivityRefutationBoundaryToEventFlow
  fromEventFlow := objectivityRefutationBoundaryFromEventFlow

instance objectivityRefutationBoundaryChapterTasteGate :
    ChapterTasteGate ObjectivityRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      objectivityRefutationBoundaryFromEventFlow
        (objectivityRefutationBoundaryToEventFlow x) = some x
    exact objectivityRefutationBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (objectivityRefutationBoundaryToEventFlow_injective heq)

instance objectivityRefutationBoundaryFieldFaithful :
    FieldFaithful ObjectivityRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := objectivityRefutationBoundaryFields
  field_faithful := objectivityRefutationBoundary_fields_faithful

instance objectivityRefutationBoundaryNontrivial :
    Nontrivial ObjectivityRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObjectivityRefutationBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObjectivityRefutationBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObjectivityRefutationBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  objectivityRefutationBoundaryChapterTasteGate

theorem ObjectivityRefutationBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      objectivityRefutationBoundaryDecodeBHist
        (objectivityRefutationBoundaryEncodeBHist h) = h) ∧
      (∀ x : ObjectivityRefutationBoundaryUp,
        objectivityRefutationBoundaryFromEventFlow
          (objectivityRefutationBoundaryToEventFlow x) = some x) ∧
      (∀ x y : ObjectivityRefutationBoundaryUp,
        objectivityRefutationBoundaryToEventFlow x =
          objectivityRefutationBoundaryToEventFlow y → x = y) ∧
      Nonempty (Nontrivial ObjectivityRefutationBoundaryUp) ∧
      Nonempty (ChapterTasteGate ObjectivityRefutationBoundaryUp) ∧
      Nonempty (FieldFaithful ObjectivityRefutationBoundaryUp) ∧
      objectivityRefutationBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
      objectivityRefutationBoundaryToEventFlow
          (ObjectivityRefutationBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
        objectivityRefutationBoundaryToEventFlow
          (ObjectivityRefutationBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact objectivityRefutationBoundaryDecode_encode_bhist
  · constructor
    · intro x
      change
        objectivityRefutationBoundaryFromEventFlow
          (objectivityRefutationBoundaryToEventFlow x) = some x
      exact objectivityRefutationBoundary_round_trip x
    · constructor
      · intro x y heq
        exact objectivityRefutationBoundaryToEventFlow_injective heq
      · constructor
        · exact ⟨objectivityRefutationBoundaryNontrivial⟩
        · constructor
          · exact ⟨objectivityRefutationBoundaryChapterTasteGate⟩
          · constructor
            · exact ⟨objectivityRefutationBoundaryFieldFaithful⟩
            · constructor
              · rfl
              · intro h
                have hx :
                    ObjectivityRefutationBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
                        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty =
                      ObjectivityRefutationBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty :=
                  objectivityRefutationBoundaryToEventFlow_injective h
                cases hx

namespace TasteGate

theorem ObjectivityRefutationBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      objectivityRefutationBoundaryDecodeBHist
        (objectivityRefutationBoundaryEncodeBHist h) = h) ∧
      (∀ x : ObjectivityRefutationBoundaryUp,
        objectivityRefutationBoundaryFromEventFlow
          (objectivityRefutationBoundaryToEventFlow x) = some x) ∧
      (∀ x y : ObjectivityRefutationBoundaryUp,
        objectivityRefutationBoundaryToEventFlow x =
          objectivityRefutationBoundaryToEventFlow y → x = y) ∧
      Nonempty (Nontrivial ObjectivityRefutationBoundaryUp) ∧
      Nonempty (ChapterTasteGate ObjectivityRefutationBoundaryUp) ∧
      Nonempty (FieldFaithful ObjectivityRefutationBoundaryUp) ∧
      objectivityRefutationBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
      objectivityRefutationBoundaryToEventFlow
          (ObjectivityRefutationBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
        objectivityRefutationBoundaryToEventFlow
          (ObjectivityRefutationBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) :=
  _root_.BEDC.Derived.ObjectivityRefutationBoundaryUp.ObjectivityRefutationBoundaryTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.ObjectivityRefutationBoundaryUp
