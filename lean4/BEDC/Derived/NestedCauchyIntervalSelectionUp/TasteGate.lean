import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedCauchyIntervalSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedCauchyIntervalSelectionUp : Type where
  | mk (I L D W R E H C P N : BHist) : NestedCauchyIntervalSelectionUp
  deriving DecidableEq

def nestedCauchyIntervalSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedCauchyIntervalSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedCauchyIntervalSelectionEncodeBHist h

def nestedCauchyIntervalSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedCauchyIntervalSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedCauchyIntervalSelectionDecodeBHist tail)

private theorem nestedCauchyIntervalSelectionDecode_encode_bhist :
    ∀ h : BHist,
      nestedCauchyIntervalSelectionDecodeBHist
          (nestedCauchyIntervalSelectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedCauchyIntervalSelectionFields :
    NestedCauchyIntervalSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedCauchyIntervalSelectionUp.mk I L D W R E H C P N =>
      [I, L, D, W, R, E, H, C, P, N]

def nestedCauchyIntervalSelectionToEventFlow :
    NestedCauchyIntervalSelectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (nestedCauchyIntervalSelectionFields x).map
      nestedCauchyIntervalSelectionEncodeBHist

private def nestedCauchyIntervalSelectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      nestedCauchyIntervalSelectionEventAtDefault index rest

def nestedCauchyIntervalSelectionFromEventFlow
    (ef : EventFlow) : Option NestedCauchyIntervalSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NestedCauchyIntervalSelectionUp.mk
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 0 ef))
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 1 ef))
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 2 ef))
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 3 ef))
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 4 ef))
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 5 ef))
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 6 ef))
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 7 ef))
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 8 ef))
      (nestedCauchyIntervalSelectionDecodeBHist
        (nestedCauchyIntervalSelectionEventAtDefault 9 ef)))

private theorem nestedCauchyIntervalSelection_round_trip :
    ∀ x : NestedCauchyIntervalSelectionUp,
      nestedCauchyIntervalSelectionFromEventFlow
          (nestedCauchyIntervalSelectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I L D W R E H C P N =>
      change
        some
          (NestedCauchyIntervalSelectionUp.mk
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist I))
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist L))
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist D))
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist W))
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist R))
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist E))
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist H))
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist C))
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist P))
            (nestedCauchyIntervalSelectionDecodeBHist
              (nestedCauchyIntervalSelectionEncodeBHist N))) =
          some (NestedCauchyIntervalSelectionUp.mk I L D W R E H C P N)
      rw [nestedCauchyIntervalSelectionDecode_encode_bhist I,
        nestedCauchyIntervalSelectionDecode_encode_bhist L,
        nestedCauchyIntervalSelectionDecode_encode_bhist D,
        nestedCauchyIntervalSelectionDecode_encode_bhist W,
        nestedCauchyIntervalSelectionDecode_encode_bhist R,
        nestedCauchyIntervalSelectionDecode_encode_bhist E,
        nestedCauchyIntervalSelectionDecode_encode_bhist H,
        nestedCauchyIntervalSelectionDecode_encode_bhist C,
        nestedCauchyIntervalSelectionDecode_encode_bhist P,
        nestedCauchyIntervalSelectionDecode_encode_bhist N]

private theorem nestedCauchyIntervalSelectionToEventFlow_injective
    {x y : NestedCauchyIntervalSelectionUp} :
    nestedCauchyIntervalSelectionToEventFlow x =
        nestedCauchyIntervalSelectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedCauchyIntervalSelectionFromEventFlow
          (nestedCauchyIntervalSelectionToEventFlow x) =
        nestedCauchyIntervalSelectionFromEventFlow
          (nestedCauchyIntervalSelectionToEventFlow y) :=
    congrArg nestedCauchyIntervalSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedCauchyIntervalSelection_round_trip x).symm
      (Eq.trans hread (nestedCauchyIntervalSelection_round_trip y)))

private theorem nestedCauchyIntervalSelection_fields_faithful :
    ∀ x y : NestedCauchyIntervalSelectionUp,
      nestedCauchyIntervalSelectionFields x =
          nestedCauchyIntervalSelectionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ L₁ D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ L₂ D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance nestedCauchyIntervalSelectionBHistCarrier :
    BHistCarrier NestedCauchyIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedCauchyIntervalSelectionToEventFlow
  fromEventFlow := nestedCauchyIntervalSelectionFromEventFlow

instance nestedCauchyIntervalSelectionChapterTasteGate :
    ChapterTasteGate NestedCauchyIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedCauchyIntervalSelectionFromEventFlow
          (nestedCauchyIntervalSelectionToEventFlow x) =
        some x
    exact nestedCauchyIntervalSelection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedCauchyIntervalSelectionToEventFlow_injective heq)

instance nestedCauchyIntervalSelectionFieldFaithful :
    FieldFaithful NestedCauchyIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedCauchyIntervalSelectionFields
  field_faithful := nestedCauchyIntervalSelection_fields_faithful

instance nestedCauchyIntervalSelectionNontrivial :
    Nontrivial NestedCauchyIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedCauchyIntervalSelectionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      NestedCauchyIntervalSelectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NestedCauchyIntervalSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedCauchyIntervalSelectionChapterTasteGate

theorem NestedCauchyIntervalSelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedCauchyIntervalSelectionDecodeBHist
          (nestedCauchyIntervalSelectionEncodeBHist h) =
        h) ∧
      (∀ x : NestedCauchyIntervalSelectionUp,
        nestedCauchyIntervalSelectionFromEventFlow
            (nestedCauchyIntervalSelectionToEventFlow x) =
          some x) ∧
        (∀ x y : NestedCauchyIntervalSelectionUp,
          nestedCauchyIntervalSelectionToEventFlow x =
              nestedCauchyIntervalSelectionToEventFlow y →
            x = y) ∧
          nestedCauchyIntervalSelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact nestedCauchyIntervalSelectionDecode_encode_bhist
  · constructor
    · exact nestedCauchyIntervalSelection_round_trip
    · constructor
      · intro x y heq
        exact nestedCauchyIntervalSelectionToEventFlow_injective heq
      · rfl

end BEDC.Derived.NestedCauchyIntervalSelectionUp
