import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AntipodalTriggerLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AntipodalTriggerLedgerUp : Type where
  | mk (S Y G T M H C P N : BHist) : AntipodalTriggerLedgerUp
  deriving DecidableEq

def antipodalTriggerLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: antipodalTriggerLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: antipodalTriggerLedgerEncodeBHist h

def antipodalTriggerLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (antipodalTriggerLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (antipodalTriggerLedgerDecodeBHist tail)

private theorem AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      antipodalTriggerLedgerDecodeBHist (antipodalTriggerLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def antipodalTriggerLedgerToEventFlow : AntipodalTriggerLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AntipodalTriggerLedgerUp.mk S Y G T M H C P N =>
      [antipodalTriggerLedgerEncodeBHist S, antipodalTriggerLedgerEncodeBHist Y,
        antipodalTriggerLedgerEncodeBHist G, antipodalTriggerLedgerEncodeBHist T,
        antipodalTriggerLedgerEncodeBHist M, antipodalTriggerLedgerEncodeBHist H,
        antipodalTriggerLedgerEncodeBHist C, antipodalTriggerLedgerEncodeBHist P,
        antipodalTriggerLedgerEncodeBHist N]

def antipodalTriggerLedgerFromEventFlow : EventFlow → Option AntipodalTriggerLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: Y :: G :: T :: M :: H :: C :: P :: N :: [] =>
      some
        (AntipodalTriggerLedgerUp.mk
          (antipodalTriggerLedgerDecodeBHist S)
          (antipodalTriggerLedgerDecodeBHist Y)
          (antipodalTriggerLedgerDecodeBHist G)
          (antipodalTriggerLedgerDecodeBHist T)
          (antipodalTriggerLedgerDecodeBHist M)
          (antipodalTriggerLedgerDecodeBHist H)
          (antipodalTriggerLedgerDecodeBHist C)
          (antipodalTriggerLedgerDecodeBHist P)
          (antipodalTriggerLedgerDecodeBHist N))
  | _ => none

private theorem AntipodalTriggerLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AntipodalTriggerLedgerUp,
      antipodalTriggerLedgerFromEventFlow (antipodalTriggerLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Y G T M H C P N =>
      rw [antipodalTriggerLedgerToEventFlow, antipodalTriggerLedgerFromEventFlow,
        AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode S,
        AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode Y,
        AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode G,
        AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode T,
        AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode M,
        AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode H,
        AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode C,
        AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode P,
        AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode N]

private theorem AntipodalTriggerLedgerToEventFlow_injective {x y : AntipodalTriggerLedgerUp} :
    antipodalTriggerLedgerToEventFlow x = antipodalTriggerLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk S₁ Y₁ G₁ T₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Y₂ G₂ T₂ M₂ H₂ C₂ P₂ N₂ =>
          injection heq with hS tail0
          injection tail0 with hY tail1
          injection tail1 with hG tail2
          injection tail2 with hT tail3
          injection tail3 with hM tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          have eqS : S₁ = S₂ := by
            have decoded := congrArg antipodalTriggerLedgerDecodeBHist hS
            rw [AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode S₁,
              AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode S₂] at decoded
            exact decoded
          have eqY : Y₁ = Y₂ := by
            have decoded := congrArg antipodalTriggerLedgerDecodeBHist hY
            rw [AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode Y₁,
              AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode Y₂] at decoded
            exact decoded
          have eqG : G₁ = G₂ := by
            have decoded := congrArg antipodalTriggerLedgerDecodeBHist hG
            rw [AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode G₁,
              AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode G₂] at decoded
            exact decoded
          have eqT : T₁ = T₂ := by
            have decoded := congrArg antipodalTriggerLedgerDecodeBHist hT
            rw [AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode T₁,
              AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode T₂] at decoded
            exact decoded
          have eqM : M₁ = M₂ := by
            have decoded := congrArg antipodalTriggerLedgerDecodeBHist hM
            rw [AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode M₁,
              AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode M₂] at decoded
            exact decoded
          have eqH : H₁ = H₂ := by
            have decoded := congrArg antipodalTriggerLedgerDecodeBHist hH
            rw [AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode H₁,
              AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode H₂] at decoded
            exact decoded
          have eqC : C₁ = C₂ := by
            have decoded := congrArg antipodalTriggerLedgerDecodeBHist hC
            rw [AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode C₁,
              AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode C₂] at decoded
            exact decoded
          have eqP : P₁ = P₂ := by
            have decoded := congrArg antipodalTriggerLedgerDecodeBHist hP
            rw [AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode P₁,
              AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode P₂] at decoded
            exact decoded
          have eqN : N₁ = N₂ := by
            have decoded := congrArg antipodalTriggerLedgerDecodeBHist hN
            rw [AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode N₁,
              AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode N₂] at decoded
            exact decoded
          subst eqS
          subst eqY
          subst eqG
          subst eqT
          subst eqM
          subst eqH
          subst eqC
          subst eqP
          subst eqN
          rfl

private def antipodalTriggerLedgerFields : AntipodalTriggerLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AntipodalTriggerLedgerUp.mk S Y G T M H C P N => [S, Y, G, T, M, H, C, P, N]

private theorem AntipodalTriggerLedgerTasteGate_single_carrier_alignment_fields :
    ∀ x y : AntipodalTriggerLedgerUp,
      antipodalTriggerLedgerFields x = antipodalTriggerLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ Y₁ G₁ T₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Y₂ G₂ T₂ M₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS tail0
          injection tail0 with hY tail1
          injection tail1 with hG tail2
          injection tail2 with hT tail3
          injection tail3 with hM tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hS
          subst hY
          subst hG
          subst hT
          subst hM
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance antipodalTriggerLedgerBHistCarrier : BHistCarrier AntipodalTriggerLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := antipodalTriggerLedgerToEventFlow
  fromEventFlow := antipodalTriggerLedgerFromEventFlow

instance antipodalTriggerLedgerChapterTasteGate :
    ChapterTasteGate AntipodalTriggerLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change antipodalTriggerLedgerFromEventFlow (antipodalTriggerLedgerToEventFlow x) = some x
    exact AntipodalTriggerLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AntipodalTriggerLedgerToEventFlow_injective heq)

instance antipodalTriggerLedgerFieldFaithful : FieldFaithful AntipodalTriggerLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := antipodalTriggerLedgerFields
  field_faithful := AntipodalTriggerLedgerTasteGate_single_carrier_alignment_fields

instance antipodalTriggerLedgerNontrivial : Nontrivial AntipodalTriggerLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AntipodalTriggerLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AntipodalTriggerLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AntipodalTriggerLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  antipodalTriggerLedgerChapterTasteGate

theorem AntipodalTriggerLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, antipodalTriggerLedgerDecodeBHist (antipodalTriggerLedgerEncodeBHist h) = h) ∧
      antipodalTriggerLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨AntipodalTriggerLedgerTasteGate_single_carrier_alignment_decode, rfl⟩

end BEDC.Derived.AntipodalTriggerLedgerUp
