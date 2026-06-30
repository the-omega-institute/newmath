import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedCompletionComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedCompletionComparisonUp : Type where
  | mk (L B Q M R S D A H C P N : BHist) : BishopLocatedCompletionComparisonUp
  deriving DecidableEq

def bishopLocatedCompletionComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedCompletionComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedCompletionComparisonEncodeBHist h

def bishopLocatedCompletionComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedCompletionComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedCompletionComparisonDecodeBHist tail)

private theorem bishopLocatedCompletionComparison_decode_encode_bhist :
    ∀ h : BHist,
      bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedCompletionComparisonFields :
    BishopLocatedCompletionComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedCompletionComparisonUp.mk L B Q M R S D A H C P N =>
      [L, B, Q, M, R, S, D, A, H, C, P, N]

def bishopLocatedCompletionComparisonToEventFlow :
    BishopLocatedCompletionComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopLocatedCompletionComparisonFields x).map
        bishopLocatedCompletionComparisonEncodeBHist

private def bishopLocatedCompletionComparisonEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopLocatedCompletionComparisonEventAtDefault index rest

def bishopLocatedCompletionComparisonFromEventFlow
    (ef : EventFlow) : Option BishopLocatedCompletionComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedCompletionComparisonUp.mk
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 0 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 1 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 2 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 3 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 4 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 5 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 6 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 7 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 8 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 9 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 10 ef))
      (bishopLocatedCompletionComparisonDecodeBHist
        (bishopLocatedCompletionComparisonEventAtDefault 11 ef)))

private theorem BishopLocatedCompletionComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedCompletionComparisonUp,
      bishopLocatedCompletionComparisonFromEventFlow
        (bishopLocatedCompletionComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L B Q M R S D A H C P N =>
      change
        some
          (BishopLocatedCompletionComparisonUp.mk
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist L))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist B))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist Q))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist M))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist R))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist S))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist D))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist A))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist H))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist C))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist P))
            (bishopLocatedCompletionComparisonDecodeBHist
              (bishopLocatedCompletionComparisonEncodeBHist N))) =
          some (BishopLocatedCompletionComparisonUp.mk L B Q M R S D A H C P N)
      rw [bishopLocatedCompletionComparison_decode_encode_bhist L,
        bishopLocatedCompletionComparison_decode_encode_bhist B,
        bishopLocatedCompletionComparison_decode_encode_bhist Q,
        bishopLocatedCompletionComparison_decode_encode_bhist M,
        bishopLocatedCompletionComparison_decode_encode_bhist R,
        bishopLocatedCompletionComparison_decode_encode_bhist S,
        bishopLocatedCompletionComparison_decode_encode_bhist D,
        bishopLocatedCompletionComparison_decode_encode_bhist A,
        bishopLocatedCompletionComparison_decode_encode_bhist H,
        bishopLocatedCompletionComparison_decode_encode_bhist C,
        bishopLocatedCompletionComparison_decode_encode_bhist P,
        bishopLocatedCompletionComparison_decode_encode_bhist N]

private theorem BishopLocatedCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopLocatedCompletionComparisonUp} :
    bishopLocatedCompletionComparisonToEventFlow x =
      bishopLocatedCompletionComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedCompletionComparisonFromEventFlow
          (bishopLocatedCompletionComparisonToEventFlow x) =
        bishopLocatedCompletionComparisonFromEventFlow
          (bishopLocatedCompletionComparisonToEventFlow y) :=
    congrArg bishopLocatedCompletionComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedCompletionComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedCompletionComparisonTasteGate_single_carrier_alignment_round_trip y)))

private theorem bishopLocatedCompletionComparison_fields_faithful :
    ∀ x y : BishopLocatedCompletionComparisonUp,
      bishopLocatedCompletionComparisonFields x =
        bishopLocatedCompletionComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ B₁ Q₁ M₁ R₁ S₁ D₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ B₂ Q₂ M₂ R₂ S₂ D₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopLocatedCompletionComparisonBHistCarrier :
    BHistCarrier BishopLocatedCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedCompletionComparisonToEventFlow
  fromEventFlow := bishopLocatedCompletionComparisonFromEventFlow

instance bishopLocatedCompletionComparisonChapterTasteGate :
    ChapterTasteGate BishopLocatedCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedCompletionComparisonFromEventFlow
        (bishopLocatedCompletionComparisonToEventFlow x) = some x
    exact BishopLocatedCompletionComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedCompletionComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance bishopLocatedCompletionComparisonFieldFaithful :
    FieldFaithful BishopLocatedCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedCompletionComparisonFields
  field_faithful := bishopLocatedCompletionComparison_fields_faithful

instance bishopLocatedCompletionComparisonNontrivial :
    Nontrivial BishopLocatedCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedCompletionComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopLocatedCompletionComparisonUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopLocatedCompletionComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedCompletionComparisonChapterTasteGate

theorem BishopLocatedCompletionComparisonTasteGate_single_carrier_alignment :
    ∃ x y : BishopLocatedCompletionComparisonUp,
      x ≠ y ∧
        bishopLocatedCompletionComparisonFields x =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty] ∧
          bishopLocatedCompletionComparisonEncodeBHist (BHist.e0 BHist.Empty) =
            [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  refine
    ⟨BishopLocatedCompletionComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BishopLocatedCompletionComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ?_, rfl, rfl⟩
  intro h
  cases h

end BEDC.Derived.BishopLocatedCompletionComparisonUp
