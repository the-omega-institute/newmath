import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DependentCodomainClosurePreservationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DependentCodomainClosurePreservationUp : Type where
  | mk :
      (Pi A a a' C0 C1 Z S I T L H R P N : BHist) →
      DependentCodomainClosurePreservationUp
  deriving DecidableEq

def dependentCodomainClosurePreservationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dependentCodomainClosurePreservationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dependentCodomainClosurePreservationEncodeBHist h

def dependentCodomainClosurePreservationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dependentCodomainClosurePreservationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dependentCodomainClosurePreservationDecodeBHist tail)

private theorem dependentCodomainClosurePreservationDecode_encode_bhist :
    ∀ h : BHist,
      dependentCodomainClosurePreservationDecodeBHist
          (dependentCodomainClosurePreservationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dependentCodomainClosurePreservationFields :
    DependentCodomainClosurePreservationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DependentCodomainClosurePreservationUp.mk Pi A a a' C0 C1 Z S I T L H R P N =>
      [Pi, A, a, a', C0, C1, Z, S, I, T, L, H, R, P, N]

def dependentCodomainClosurePreservationToEventFlow :
    DependentCodomainClosurePreservationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (dependentCodomainClosurePreservationFields x).map
        dependentCodomainClosurePreservationEncodeBHist

private def dependentCodomainClosurePreservationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      dependentCodomainClosurePreservationEventAtDefault index rest

def dependentCodomainClosurePreservationFromEventFlow
    (ef : EventFlow) : Option DependentCodomainClosurePreservationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DependentCodomainClosurePreservationUp.mk
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 0 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 1 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 2 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 3 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 4 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 5 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 6 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 7 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 8 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 9 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 10 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 11 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 12 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 13 ef))
      (dependentCodomainClosurePreservationDecodeBHist
        (dependentCodomainClosurePreservationEventAtDefault 14 ef)))

private theorem dependentCodomainClosurePreservation_round_trip :
    ∀ x : DependentCodomainClosurePreservationUp,
      dependentCodomainClosurePreservationFromEventFlow
          (dependentCodomainClosurePreservationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Pi A a a' C0 C1 Z S I T L H R P N =>
      change
        some
            (DependentCodomainClosurePreservationUp.mk
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist Pi))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist A))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist a))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist a'))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist C0))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist C1))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist Z))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist S))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist I))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist T))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist L))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist H))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist R))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist P))
              (dependentCodomainClosurePreservationDecodeBHist
                (dependentCodomainClosurePreservationEncodeBHist N))) =
          some (DependentCodomainClosurePreservationUp.mk Pi A a a' C0 C1 Z S I T L H R P N)
      rw [dependentCodomainClosurePreservationDecode_encode_bhist Pi]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist A]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist a]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist a']
      rw [dependentCodomainClosurePreservationDecode_encode_bhist C0]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist C1]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist Z]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist S]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist I]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist T]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist L]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist H]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist R]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist P]
      rw [dependentCodomainClosurePreservationDecode_encode_bhist N]

private theorem dependentCodomainClosurePreservationToEventFlow_injective
    {x y : DependentCodomainClosurePreservationUp} :
    dependentCodomainClosurePreservationToEventFlow x =
        dependentCodomainClosurePreservationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dependentCodomainClosurePreservationFromEventFlow
          (dependentCodomainClosurePreservationToEventFlow x) =
        dependentCodomainClosurePreservationFromEventFlow
          (dependentCodomainClosurePreservationToEventFlow y) :=
    congrArg dependentCodomainClosurePreservationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dependentCodomainClosurePreservation_round_trip x).symm
      (Eq.trans hread (dependentCodomainClosurePreservation_round_trip y)))

private theorem dependentCodomainClosurePreservation_fields_faithful :
    ∀ x y : DependentCodomainClosurePreservationUp,
      dependentCodomainClosurePreservationFields x =
        dependentCodomainClosurePreservationFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Pi₁ A₁ a₁ a'₁ C0₁ C1₁ Z₁ S₁ I₁ T₁ L₁ H₁ R₁ P₁ N₁ =>
      cases y with
      | mk Pi₂ A₂ a₂ a'₂ C0₂ C1₂ Z₂ S₂ I₂ T₂ L₂ H₂ R₂ P₂ N₂ =>
          cases hfields
          rfl

instance dependentCodomainClosurePreservationBHistCarrier :
    BHistCarrier DependentCodomainClosurePreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dependentCodomainClosurePreservationToEventFlow
  fromEventFlow := dependentCodomainClosurePreservationFromEventFlow

instance dependentCodomainClosurePreservationChapterTasteGate :
    ChapterTasteGate DependentCodomainClosurePreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dependentCodomainClosurePreservationFromEventFlow
          (dependentCodomainClosurePreservationToEventFlow x) =
        some x
    exact dependentCodomainClosurePreservation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dependentCodomainClosurePreservationToEventFlow_injective heq)

instance dependentCodomainClosurePreservationFieldFaithful :
    FieldFaithful DependentCodomainClosurePreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dependentCodomainClosurePreservationFields
  field_faithful := dependentCodomainClosurePreservation_fields_faithful

instance dependentCodomainClosurePreservationNontrivial :
    Nontrivial DependentCodomainClosurePreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DependentCodomainClosurePreservationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DependentCodomainClosurePreservationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DependentCodomainClosurePreservationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dependentCodomainClosurePreservationChapterTasteGate

theorem DependentCodomainClosurePreservationUp_single_carrier_alignment :
    (∀ h : BHist,
      dependentCodomainClosurePreservationDecodeBHist
          (dependentCodomainClosurePreservationEncodeBHist h) =
        h) ∧
      (∀ x : DependentCodomainClosurePreservationUp,
        dependentCodomainClosurePreservationFromEventFlow
            (dependentCodomainClosurePreservationToEventFlow x) =
          some x) ∧
        (∀ x y : DependentCodomainClosurePreservationUp,
          dependentCodomainClosurePreservationToEventFlow x =
              dependentCodomainClosurePreservationToEventFlow y →
            x = y) ∧
          dependentCodomainClosurePreservationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dependentCodomainClosurePreservationDecode_encode_bhist
  · constructor
    · exact dependentCodomainClosurePreservation_round_trip
    · constructor
      · intro x y heq
        exact dependentCodomainClosurePreservationToEventFlow_injective heq
      · rfl

end BEDC.Derived.DependentCodomainClosurePreservationUp
