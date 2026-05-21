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
    FiniteErrorBudgetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (FiniteErrorBudgetTasteGate_single_carrier_alignment_fields x).map
      FiniteErrorBudgetTasteGate_single_carrier_alignment_encodeBHist

def FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option FiniteErrorBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | n :: eps :: b :: d :: t :: r :: e :: p :: cert :: [] =>
      some
        (FiniteErrorBudgetUp.mk
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist n)
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist eps)
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist b)
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist d)
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist t)
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist r)
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist e)
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist p)
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_decodeBHist cert))
  | _ => none

private theorem FiniteErrorBudgetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteErrorBudgetUp,
      FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk n eps b d t r e p cert =>
      simp only [FiniteErrorBudgetTasteGate_single_carrier_alignment_toEventFlow,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_fields,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, FiniteErrorBudgetTasteGate_single_carrier_alignment_decode_encode]

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
          injection hfields with hn tail0
          injection tail0 with heps tail1
          injection tail1 with hb tail2
          injection tail2 with hd tail3
          injection tail3 with ht tail4
          injection tail4 with hr tail5
          injection tail5 with he tail6
          injection tail6 with hp tail7
          injection tail7 with hcert _
          subst hn
          subst heps
          subst hb
          subst hd
          subst ht
          subst hr
          subst he
          subst hp
          subst hcert
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
      (∀ x y : FiniteErrorBudgetUp,
        FiniteErrorBudgetTasteGate_single_carrier_alignment_fields x =
            FiniteErrorBudgetTasteGate_single_carrier_alignment_fields y →
          x = y) ∧
      (∃ x y : FiniteErrorBudgetUp, x ≠ y) ∧
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
  · exact FiniteErrorBudgetTasteGate_single_carrier_alignment_fields_faithful
  constructor
  · exact
      ⟨FiniteErrorBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        FiniteErrorBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩
  constructor
  · rfl
  · rfl

end BEDC.Derived.FiniteErrorBudgetUp.TasteGate
