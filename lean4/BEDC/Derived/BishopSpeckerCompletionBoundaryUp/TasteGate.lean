import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopSpeckerCompletionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopSpeckerCompletionBoundaryUp : Type where
  | mk (S L W O A R D E H C P N : BHist) : BishopSpeckerCompletionBoundaryUp
  deriving DecidableEq

def bishopSpeckerCompletionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopSpeckerCompletionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopSpeckerCompletionBoundaryEncodeBHist h

def bishopSpeckerCompletionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopSpeckerCompletionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopSpeckerCompletionBoundaryDecodeBHist tail)

private theorem BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopSpeckerCompletionBoundaryFields :
    BishopSpeckerCompletionBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopSpeckerCompletionBoundaryUp.mk S L W O A R D E H C P N =>
      [S, L, W, O, A, R, D, E, H, C, P, N]

def bishopSpeckerCompletionBoundaryToEventFlow :
    BishopSpeckerCompletionBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopSpeckerCompletionBoundaryFields x).map
      bishopSpeckerCompletionBoundaryEncodeBHist

private def bishopSpeckerCompletionBoundaryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopSpeckerCompletionBoundaryEventAtDefault index rest

def bishopSpeckerCompletionBoundaryFromEventFlow
    (ef : EventFlow) : Option BishopSpeckerCompletionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopSpeckerCompletionBoundaryUp.mk
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 0 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 1 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 2 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 3 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 4 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 5 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 6 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 7 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 8 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 9 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 10 ef))
      (bishopSpeckerCompletionBoundaryDecodeBHist
        (bishopSpeckerCompletionBoundaryEventAtDefault 11 ef)))

private theorem BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopSpeckerCompletionBoundaryUp,
      bishopSpeckerCompletionBoundaryFromEventFlow
        (bishopSpeckerCompletionBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S L W O A R D E H C P N =>
      change
        some
          (BishopSpeckerCompletionBoundaryUp.mk
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist S))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist L))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist W))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist O))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist A))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist R))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist D))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist E))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist H))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist C))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist P))
            (bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist N))) =
          some (BishopSpeckerCompletionBoundaryUp.mk S L W O A R D E H C P N)
      rw [BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode S,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode L,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode W,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode O,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode A,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode R,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode D,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode E,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode H,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode C,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode P,
        BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem BishopSpeckerCompletionBoundaryToEventFlow_injective
    {x y : BishopSpeckerCompletionBoundaryUp} :
    bishopSpeckerCompletionBoundaryToEventFlow x =
      bishopSpeckerCompletionBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopSpeckerCompletionBoundaryFromEventFlow
          (bishopSpeckerCompletionBoundaryToEventFlow x) =
        bishopSpeckerCompletionBoundaryFromEventFlow
          (bishopSpeckerCompletionBoundaryToEventFlow y) :=
    congrArg bishopSpeckerCompletionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopSpeckerCompletionBoundaryUp,
      bishopSpeckerCompletionBoundaryFields x =
        bishopSpeckerCompletionBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 L1 W1 O1 A1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 L2 W2 O2 A2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopSpeckerCompletionBoundaryBHistCarrier :
    BHistCarrier BishopSpeckerCompletionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopSpeckerCompletionBoundaryToEventFlow
  fromEventFlow := bishopSpeckerCompletionBoundaryFromEventFlow

instance bishopSpeckerCompletionBoundaryChapterTasteGate :
    ChapterTasteGate BishopSpeckerCompletionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopSpeckerCompletionBoundaryFromEventFlow
        (bishopSpeckerCompletionBoundaryToEventFlow x) = some x
    exact
      BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopSpeckerCompletionBoundaryToEventFlow_injective heq)

instance bishopSpeckerCompletionBoundaryFieldFaithful :
    FieldFaithful BishopSpeckerCompletionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopSpeckerCompletionBoundaryFields
  field_faithful :=
    BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_fields

instance bishopSpeckerCompletionBoundaryNontrivial :
    Nontrivial BishopSpeckerCompletionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopSpeckerCompletionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BishopSpeckerCompletionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopSpeckerCompletionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopSpeckerCompletionBoundaryChapterTasteGate

theorem BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopSpeckerCompletionBoundaryUp) ∧
      Nonempty (FieldFaithful BishopSpeckerCompletionBoundaryUp) ∧
        Nonempty
          (BEDC.Meta.TasteGate.Nontrivial BishopSpeckerCompletionBoundaryUp) ∧
          (∀ h : BHist,
            bishopSpeckerCompletionBoundaryDecodeBHist
              (bishopSpeckerCompletionBoundaryEncodeBHist h) = h) ∧
            (∀ x : BishopSpeckerCompletionBoundaryUp,
              bishopSpeckerCompletionBoundaryFromEventFlow
                (bishopSpeckerCompletionBoundaryToEventFlow x) = some x) ∧
              bishopSpeckerCompletionBoundaryEncodeBHist BHist.Empty =
                ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨bishopSpeckerCompletionBoundaryChapterTasteGate⟩,
      ⟨bishopSpeckerCompletionBoundaryFieldFaithful⟩,
      ⟨bishopSpeckerCompletionBoundaryNontrivial⟩,
      BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_decode,
      BishopSpeckerCompletionBoundaryTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.BishopSpeckerCompletionBoundaryUp
