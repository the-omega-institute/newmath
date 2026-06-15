import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IsaacsEquationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IsaacsEquationUp : Type where
  | mk (G A B V D E O R H C P N : BHist) : IsaacsEquationUp
  deriving DecidableEq

def isaacsEquationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: isaacsEquationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: isaacsEquationEncodeBHist h

def isaacsEquationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (isaacsEquationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (isaacsEquationDecodeBHist tail)

private theorem IsaacsEquationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, isaacsEquationDecodeBHist (isaacsEquationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def isaacsEquationFields : IsaacsEquationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IsaacsEquationUp.mk G A B V D E O R H C P N => [G, A, B, V, D, E, O, R, H, C, P, N]

def isaacsEquationToEventFlow : IsaacsEquationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (isaacsEquationFields x).map isaacsEquationEncodeBHist

private def isaacsEquationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => isaacsEquationEventAtDefault index rest

def isaacsEquationFromEventFlow (ef : EventFlow) : Option IsaacsEquationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IsaacsEquationUp.mk
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 0 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 1 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 2 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 3 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 4 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 5 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 6 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 7 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 8 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 9 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 10 ef))
      (isaacsEquationDecodeBHist (isaacsEquationEventAtDefault 11 ef)))

private theorem IsaacsEquationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IsaacsEquationUp,
      isaacsEquationFromEventFlow (isaacsEquationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G A B V D E O R H C P N =>
      change
        some
          (IsaacsEquationUp.mk
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist G))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist A))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist B))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist V))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist D))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist E))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist O))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist R))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist H))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist C))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist P))
            (isaacsEquationDecodeBHist (isaacsEquationEncodeBHist N))) =
          some (IsaacsEquationUp.mk G A B V D E O R H C P N)
      rw [IsaacsEquationTasteGate_single_carrier_alignment_decode G,
        IsaacsEquationTasteGate_single_carrier_alignment_decode A,
        IsaacsEquationTasteGate_single_carrier_alignment_decode B,
        IsaacsEquationTasteGate_single_carrier_alignment_decode V,
        IsaacsEquationTasteGate_single_carrier_alignment_decode D,
        IsaacsEquationTasteGate_single_carrier_alignment_decode E,
        IsaacsEquationTasteGate_single_carrier_alignment_decode O,
        IsaacsEquationTasteGate_single_carrier_alignment_decode R,
        IsaacsEquationTasteGate_single_carrier_alignment_decode H,
        IsaacsEquationTasteGate_single_carrier_alignment_decode C,
        IsaacsEquationTasteGate_single_carrier_alignment_decode P,
        IsaacsEquationTasteGate_single_carrier_alignment_decode N]

private theorem IsaacsEquationTasteGate_single_carrier_alignment_injective
    {x y : IsaacsEquationUp} :
    isaacsEquationToEventFlow x = isaacsEquationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      isaacsEquationFromEventFlow (isaacsEquationToEventFlow x) =
        isaacsEquationFromEventFlow (isaacsEquationToEventFlow y) :=
    congrArg isaacsEquationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (IsaacsEquationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IsaacsEquationTasteGate_single_carrier_alignment_round_trip y)))

private theorem IsaacsEquationTasteGate_single_carrier_alignment_fields :
    ∀ x y : IsaacsEquationUp, isaacsEquationFields x = isaacsEquationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ A₁ B₁ V₁ D₁ E₁ O₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk G₂ A₂ B₂ V₂ D₂ E₂ O₂ R₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hG tail0
          injection tail0 with hA tail1
          injection tail1 with hB tail2
          injection tail2 with hV tail3
          injection tail3 with hD tail4
          injection tail4 with hE tail5
          injection tail5 with hO tail6
          injection tail6 with hR tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hG
          subst hA
          subst hB
          subst hV
          subst hD
          subst hE
          subst hO
          subst hR
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance isaacsEquationBHistCarrier : BHistCarrier IsaacsEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := isaacsEquationToEventFlow
  fromEventFlow := isaacsEquationFromEventFlow

instance isaacsEquationChapterTasteGate : ChapterTasteGate IsaacsEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change isaacsEquationFromEventFlow (isaacsEquationToEventFlow x) = some x
    exact IsaacsEquationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IsaacsEquationTasteGate_single_carrier_alignment_injective heq)

instance isaacsEquationFieldFaithful : FieldFaithful IsaacsEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := isaacsEquationFields
  field_faithful := IsaacsEquationTasteGate_single_carrier_alignment_fields

instance isaacsEquationNontrivial : Nontrivial IsaacsEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IsaacsEquationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      IsaacsEquationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate IsaacsEquationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  isaacsEquationChapterTasteGate

def taste_gate_witness : FieldFaithful IsaacsEquationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  isaacsEquationFieldFaithful

theorem IsaacsEquationTasteGate_single_carrier_alignment :
    (∀ h : BHist, isaacsEquationDecodeBHist (isaacsEquationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier IsaacsEquationUp) ∧
        Nonempty (ChapterTasteGate IsaacsEquationUp) ∧
          Nonempty (FieldFaithful IsaacsEquationUp) ∧
            Nonempty (BEDC.Meta.TasteGate.Nontrivial IsaacsEquationUp) ∧
              isaacsEquationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨IsaacsEquationTasteGate_single_carrier_alignment_decode,
      ⟨isaacsEquationBHistCarrier⟩,
      ⟨isaacsEquationChapterTasteGate⟩,
      ⟨isaacsEquationFieldFaithful⟩,
      ⟨isaacsEquationNontrivial⟩,
      rfl⟩

end BEDC.Derived.IsaacsEquationUp
