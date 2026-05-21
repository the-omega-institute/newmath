import BEDC.Derived.FiniteErrorBudgetUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteErrorBudgetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteErrorBudgetUp : Type where
  | mk (n eps b d t r e p cert : BHist) : FiniteErrorBudgetUp
  deriving DecidableEq

def FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist h

def FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FiniteErrorBudgetTasteGate_single_carrier_alignment_fields :
    FiniteErrorBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteErrorBudgetUp.mk n eps b d t r e p cert => [n, eps, b, d, t, r, e, p, cert]

def FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow :
    FiniteErrorBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
    (FiniteErrorBudgetTasteGate_single_carrier_alignment_fields x).map
      FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist

private def FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt n rest

private def FiniteErrorBudgetTasteGate_single_carrier_alignment_lengthEq :
    Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => FiniteErrorBudgetTasteGate_single_carrier_alignment_lengthEq n rest

def FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow
    (flow : EventFlow) : Option FiniteErrorBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match FiniteErrorBudgetTasteGate_single_carrier_alignment_lengthEq 9 flow with
  | true =>
      some
        (FiniteErrorBudgetUp.mk
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt 0 flow))
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt 1 flow))
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt 2 flow))
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt 3 flow))
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt 4 flow))
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt 5 flow))
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt 6 flow))
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt 7 flow))
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_rawAt 8 flow)))
  | false => none

private theorem FiniteErrorBudgetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteErrorBudgetUp,
      FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk n eps b d t r e p cert =>
      change
        some
          (FiniteErrorBudgetUp.mk
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
              (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist n))
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
              (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist eps))
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
              (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist b))
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
              (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist d))
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
              (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist t))
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
              (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist r))
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
              (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist e))
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
              (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist p))
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
              (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist cert))) =
          some (FiniteErrorBudgetUp.mk n eps b d t r e p cert)
      rw [FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode n,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode eps,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode b,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode d,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode t,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode r,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode e,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode p,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode cert]

private theorem FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteErrorBudgetUp} :
    FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow x =
        FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow x) =
        FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteErrorBudgetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteErrorBudgetTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteErrorBudgetTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FiniteErrorBudgetUp,
      FiniteErrorBudgetTasteGate_single_carrier_alignment_fields x =
          FiniteErrorBudgetTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk n₁ eps₁ b₁ d₁ t₁ r₁ e₁ p₁ cert₁ =>
      cases y with
      | mk n₂ eps₂ b₂ d₂ t₂ r₂ e₂ p₂ cert₂ =>
          cases hfields
          rfl

instance FiniteErrorBudgetTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier FiniteErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow

instance FiniteErrorBudgetTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate FiniteErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact FiniteErrorBudgetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance FiniteErrorBudgetTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful FiniteErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := FiniteErrorBudgetTasteGate_single_carrier_alignment_fields
  field_faithful := FiniteErrorBudgetTasteGate_single_carrier_alignment_fields_faithful

instance FiniteErrorBudgetTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial FiniteErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteErrorBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteErrorBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteErrorBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FiniteErrorBudgetTasteGate_single_carrier_alignment_ChapterTasteGate

theorem FiniteErrorBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist
            (FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      FiniteErrorBudgetTasteGate_single_carrier_alignment_fields
          (FiniteErrorBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] ∧
      FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow
          (FiniteErrorBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode
  constructor
  · rfl
  · rfl

end BEDC.Derived.FiniteErrorBudgetUp.TasteGate
