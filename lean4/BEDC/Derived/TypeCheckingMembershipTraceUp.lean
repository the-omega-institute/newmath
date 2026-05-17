import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypeCheckingMembershipTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypeCheckingMembershipTraceUp : Type where
  | mk : (M D R S H C P N : BHist) → TypeCheckingMembershipTraceUp
  deriving DecidableEq

def typeCheckingMembershipTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typeCheckingMembershipTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typeCheckingMembershipTraceEncodeBHist h

def typeCheckingMembershipTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typeCheckingMembershipTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typeCheckingMembershipTraceDecodeBHist tail)

private theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      typeCheckingMembershipTraceDecodeBHist
        (typeCheckingMembershipTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def typeCheckingMembershipTraceFields :
    TypeCheckingMembershipTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TypeCheckingMembershipTraceUp.mk M D R S H C P N => [M, D, R, S, H, C, P, N]

def typeCheckingMembershipTraceToEventFlow :
    TypeCheckingMembershipTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TypeCheckingMembershipTraceUp.mk M D R S H C P N =>
      [[BMark.b0],
        typeCheckingMembershipTraceEncodeBHist M,
        [BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        typeCheckingMembershipTraceEncodeBHist N]

private def typeCheckingMembershipTraceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => typeCheckingMembershipTraceEventAtDefault index rest

def typeCheckingMembershipTraceFromEventFlow
    (ef : EventFlow) : Option TypeCheckingMembershipTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TypeCheckingMembershipTraceUp.mk
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 1 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 3 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 5 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 7 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 9 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 11 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 13 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 15 ef)))

private theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TypeCheckingMembershipTraceUp,
      typeCheckingMembershipTraceFromEventFlow
        (typeCheckingMembershipTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D R S H C P N =>
      change
        some
          (TypeCheckingMembershipTraceUp.mk
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist M))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist D))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist R))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist S))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist H))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist C))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist P))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist N))) =
          some (TypeCheckingMembershipTraceUp.mk M D R S H C P N)
      rw [TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode M,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode D,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode R,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode S,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode H,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode C,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode P,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode N]

private theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_injective
    {x y : TypeCheckingMembershipTraceUp} :
    typeCheckingMembershipTraceToEventFlow x =
      typeCheckingMembershipTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typeCheckingMembershipTraceFromEventFlow (typeCheckingMembershipTraceToEventFlow x) =
        typeCheckingMembershipTraceFromEventFlow (typeCheckingMembershipTraceToEventFlow y) :=
    congrArg typeCheckingMembershipTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip y)))

private theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_fields :
    ∀ x y : TypeCheckingMembershipTraceUp,
      typeCheckingMembershipTraceFields x = typeCheckingMembershipTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ D₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ D₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance typeCheckingMembershipTraceBHistCarrier :
    BHistCarrier TypeCheckingMembershipTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typeCheckingMembershipTraceToEventFlow
  fromEventFlow := typeCheckingMembershipTraceFromEventFlow

instance typeCheckingMembershipTraceChapterTasteGate :
    ChapterTasteGate TypeCheckingMembershipTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      typeCheckingMembershipTraceFromEventFlow
        (typeCheckingMembershipTraceToEventFlow x) = some x
    exact TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_injective heq)

instance typeCheckingMembershipTraceFieldFaithful :
    FieldFaithful TypeCheckingMembershipTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := typeCheckingMembershipTraceFields
  field_faithful := TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_fields

instance typeCheckingMembershipTraceNontrivial :
    Nontrivial TypeCheckingMembershipTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TypeCheckingMembershipTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TypeCheckingMembershipTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TypeCheckingMembershipTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  typeCheckingMembershipTraceChapterTasteGate

theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      typeCheckingMembershipTraceDecodeBHist
        (typeCheckingMembershipTraceEncodeBHist h) = h) ∧
      (∀ x : TypeCheckingMembershipTraceUp,
        typeCheckingMembershipTraceFromEventFlow
          (typeCheckingMembershipTraceToEventFlow x) = some x) ∧
        (∀ x y : TypeCheckingMembershipTraceUp,
          typeCheckingMembershipTraceToEventFlow x =
            typeCheckingMembershipTraceToEventFlow y → x = y) ∧
          typeCheckingMembershipTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.TypeCheckingMembershipTraceUp
