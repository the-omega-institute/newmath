import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalizationEvidenceBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalizationEvidenceBudgetUp : Type where
  | mk (A C K S P R J I F G D H T Q N : BHist) : NormalizationEvidenceBudgetUp
  deriving DecidableEq

private def normalizationEvidenceBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalizationEvidenceBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalizationEvidenceBudgetEncodeBHist h

private def normalizationEvidenceBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalizationEvidenceBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalizationEvidenceBudgetDecodeBHist tail)

private theorem normalizationEvidenceBudget_decode_encode_bhist :
    ∀ h : BHist,
      normalizationEvidenceBudgetDecodeBHist (normalizationEvidenceBudgetEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def normalizationEvidenceBudgetFields :
    NormalizationEvidenceBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalizationEvidenceBudgetUp.mk A C K S P R J I F G D H T Q N =>
      [A, C, K, S, P, R, J, I, F, G, D, H, T, Q, N]

private def normalizationEvidenceBudgetToEventFlow :
    NormalizationEvidenceBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NormalizationEvidenceBudgetUp.mk A C K S P R J I F G D H T Q N =>
      [normalizationEvidenceBudgetEncodeBHist A,
        normalizationEvidenceBudgetEncodeBHist C,
        normalizationEvidenceBudgetEncodeBHist K,
        normalizationEvidenceBudgetEncodeBHist S,
        normalizationEvidenceBudgetEncodeBHist P,
        normalizationEvidenceBudgetEncodeBHist R,
        normalizationEvidenceBudgetEncodeBHist J,
        normalizationEvidenceBudgetEncodeBHist I,
        normalizationEvidenceBudgetEncodeBHist F,
        normalizationEvidenceBudgetEncodeBHist G,
        normalizationEvidenceBudgetEncodeBHist D,
        normalizationEvidenceBudgetEncodeBHist H,
        normalizationEvidenceBudgetEncodeBHist T,
        normalizationEvidenceBudgetEncodeBHist Q,
        normalizationEvidenceBudgetEncodeBHist N]

private def normalizationEvidenceBudgetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => normalizationEvidenceBudgetEventAtDefault index rest

private def normalizationEvidenceBudgetFromEventFlow :
    EventFlow → Option NormalizationEvidenceBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (NormalizationEvidenceBudgetUp.mk
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 0 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 1 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 2 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 3 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 4 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 5 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 6 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 7 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 8 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 9 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 10 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 11 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 12 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 13 ef))
        (normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEventAtDefault 14 ef)))

private theorem normalizationEvidenceBudget_round_trip :
    ∀ x : NormalizationEvidenceBudgetUp,
      normalizationEvidenceBudgetFromEventFlow
          (normalizationEvidenceBudgetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A C K S P R J I F G D H T Q N =>
      change
        some
          (NormalizationEvidenceBudgetUp.mk
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist A))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist C))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist K))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist S))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist P))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist R))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist J))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist I))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist F))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist G))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist D))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist H))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist T))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist Q))
            (normalizationEvidenceBudgetDecodeBHist
              (normalizationEvidenceBudgetEncodeBHist N))) =
          some (NormalizationEvidenceBudgetUp.mk A C K S P R J I F G D H T Q N)
      rw [normalizationEvidenceBudget_decode_encode_bhist A,
        normalizationEvidenceBudget_decode_encode_bhist C,
        normalizationEvidenceBudget_decode_encode_bhist K,
        normalizationEvidenceBudget_decode_encode_bhist S,
        normalizationEvidenceBudget_decode_encode_bhist P,
        normalizationEvidenceBudget_decode_encode_bhist R,
        normalizationEvidenceBudget_decode_encode_bhist J,
        normalizationEvidenceBudget_decode_encode_bhist I,
        normalizationEvidenceBudget_decode_encode_bhist F,
        normalizationEvidenceBudget_decode_encode_bhist G,
        normalizationEvidenceBudget_decode_encode_bhist D,
        normalizationEvidenceBudget_decode_encode_bhist H,
        normalizationEvidenceBudget_decode_encode_bhist T,
        normalizationEvidenceBudget_decode_encode_bhist Q,
        normalizationEvidenceBudget_decode_encode_bhist N]

private theorem normalizationEvidenceBudgetToEventFlow_injective
    {x y : NormalizationEvidenceBudgetUp} :
    normalizationEvidenceBudgetToEventFlow x =
        normalizationEvidenceBudgetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalizationEvidenceBudgetFromEventFlow
          (normalizationEvidenceBudgetToEventFlow x) =
        normalizationEvidenceBudgetFromEventFlow
          (normalizationEvidenceBudgetToEventFlow y) :=
    congrArg normalizationEvidenceBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (normalizationEvidenceBudget_round_trip x).symm
      (Eq.trans hread (normalizationEvidenceBudget_round_trip y)))

private theorem normalizationEvidenceBudget_fields_faithful :
    ∀ x y : NormalizationEvidenceBudgetUp,
      normalizationEvidenceBudgetFields x = normalizationEvidenceBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ C₁ K₁ S₁ P₁ R₁ J₁ I₁ F₁ G₁ D₁ H₁ T₁ Q₁ N₁ =>
      cases y with
      | mk A₂ C₂ K₂ S₂ P₂ R₂ J₂ I₂ F₂ G₂ D₂ H₂ T₂ Q₂ N₂ =>
          cases hfields
          rfl

instance normalizationEvidenceBudgetBHistCarrier :
    BHistCarrier NormalizationEvidenceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalizationEvidenceBudgetToEventFlow
  fromEventFlow := normalizationEvidenceBudgetFromEventFlow

instance normalizationEvidenceBudgetChapterTasteGate :
    ChapterTasteGate NormalizationEvidenceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      normalizationEvidenceBudgetFromEventFlow
          (normalizationEvidenceBudgetToEventFlow x) =
        some x
    exact normalizationEvidenceBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (normalizationEvidenceBudgetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NormalizationEvidenceBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  normalizationEvidenceBudgetChapterTasteGate

instance normalizationEvidenceBudgetFieldFaithful :
    FieldFaithful NormalizationEvidenceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := normalizationEvidenceBudgetFields
  field_faithful := normalizationEvidenceBudget_fields_faithful

instance normalizationEvidenceBudgetNontrivial :
    Nontrivial NormalizationEvidenceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NormalizationEvidenceBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NormalizationEvidenceBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem NormalizationEvidenceBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      normalizationEvidenceBudgetDecodeBHist
          (normalizationEvidenceBudgetEncodeBHist h) =
        h) ∧
      (∀ x : NormalizationEvidenceBudgetUp,
        normalizationEvidenceBudgetFromEventFlow
            (normalizationEvidenceBudgetToEventFlow x) =
          some x) ∧
        (∀ x y : NormalizationEvidenceBudgetUp,
          normalizationEvidenceBudgetToEventFlow x = normalizationEvidenceBudgetToEventFlow y →
            x = y) ∧
          (∀ x y : NormalizationEvidenceBudgetUp,
            normalizationEvidenceBudgetFields x = normalizationEvidenceBudgetFields y →
              x = y) ∧
            (∃ x y : NormalizationEvidenceBudgetUp, x ≠ y) ∧
              normalizationEvidenceBudgetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨normalizationEvidenceBudget_decode_encode_bhist,
      normalizationEvidenceBudget_round_trip,
      (fun _ _ heq => normalizationEvidenceBudgetToEventFlow_injective heq),
      normalizationEvidenceBudget_fields_faithful,
      ⟨NormalizationEvidenceBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        NormalizationEvidenceBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.NormalizationEvidenceBudgetUp
