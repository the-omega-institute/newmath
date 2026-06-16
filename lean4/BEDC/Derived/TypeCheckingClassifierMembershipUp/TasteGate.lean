import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypeCheckingClassifierMembershipUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypeCheckingClassifierMembershipUp : Type where
  | mk (T J E D S Q H C P N : BHist) : TypeCheckingClassifierMembershipUp
  deriving DecidableEq

def typeCheckingClassifierMembershipEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typeCheckingClassifierMembershipEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typeCheckingClassifierMembershipEncodeBHist h

def typeCheckingClassifierMembershipDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typeCheckingClassifierMembershipDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typeCheckingClassifierMembershipDecodeBHist tail)

private theorem typeCheckingClassifierMembership_decode_encode_bhist :
    ∀ h : BHist,
      typeCheckingClassifierMembershipDecodeBHist
        (typeCheckingClassifierMembershipEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def typeCheckingClassifierMembershipFields :
    TypeCheckingClassifierMembershipUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TypeCheckingClassifierMembershipUp.mk T J E D S Q H C P N =>
      [T, J, E, D, S, Q, H, C, P, N]

def typeCheckingClassifierMembershipToEventFlow :
    TypeCheckingClassifierMembershipUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map typeCheckingClassifierMembershipEncodeBHist
        (typeCheckingClassifierMembershipFields x)

def typeCheckingClassifierMembershipFromEventFlow :
    EventFlow → Option TypeCheckingClassifierMembershipUp
  -- BEDC touchpoint anchor: BHist BMark
  | [T, J, E, D, S, Q, H, C, P, N] =>
      some
        (TypeCheckingClassifierMembershipUp.mk
          (typeCheckingClassifierMembershipDecodeBHist T)
          (typeCheckingClassifierMembershipDecodeBHist J)
          (typeCheckingClassifierMembershipDecodeBHist E)
          (typeCheckingClassifierMembershipDecodeBHist D)
          (typeCheckingClassifierMembershipDecodeBHist S)
          (typeCheckingClassifierMembershipDecodeBHist Q)
          (typeCheckingClassifierMembershipDecodeBHist H)
          (typeCheckingClassifierMembershipDecodeBHist C)
          (typeCheckingClassifierMembershipDecodeBHist P)
          (typeCheckingClassifierMembershipDecodeBHist N))
  | _ => none

private theorem typeCheckingClassifierMembership_round_trip :
    ∀ x : TypeCheckingClassifierMembershipUp,
      typeCheckingClassifierMembershipFromEventFlow
        (typeCheckingClassifierMembershipToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T J E D S Q H C P N =>
      change
        some
          (TypeCheckingClassifierMembershipUp.mk
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist T))
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist J))
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist E))
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist D))
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist S))
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist Q))
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist H))
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist C))
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist P))
            (typeCheckingClassifierMembershipDecodeBHist
              (typeCheckingClassifierMembershipEncodeBHist N))) =
          some (TypeCheckingClassifierMembershipUp.mk T J E D S Q H C P N)
      rw [typeCheckingClassifierMembership_decode_encode_bhist T,
        typeCheckingClassifierMembership_decode_encode_bhist J,
        typeCheckingClassifierMembership_decode_encode_bhist E,
        typeCheckingClassifierMembership_decode_encode_bhist D,
        typeCheckingClassifierMembership_decode_encode_bhist S,
        typeCheckingClassifierMembership_decode_encode_bhist Q,
        typeCheckingClassifierMembership_decode_encode_bhist H,
        typeCheckingClassifierMembership_decode_encode_bhist C,
        typeCheckingClassifierMembership_decode_encode_bhist P,
        typeCheckingClassifierMembership_decode_encode_bhist N]

private theorem typeCheckingClassifierMembershipToEventFlow_injective
    {x y : TypeCheckingClassifierMembershipUp} :
    typeCheckingClassifierMembershipToEventFlow x =
        typeCheckingClassifierMembershipToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typeCheckingClassifierMembershipFromEventFlow
          (typeCheckingClassifierMembershipToEventFlow x) =
        typeCheckingClassifierMembershipFromEventFlow
          (typeCheckingClassifierMembershipToEventFlow y) :=
    congrArg typeCheckingClassifierMembershipFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (typeCheckingClassifierMembership_round_trip x).symm
      (Eq.trans hread (typeCheckingClassifierMembership_round_trip y)))

private theorem typeCheckingClassifierMembership_field_faithful :
    ∀ x y : TypeCheckingClassifierMembershipUp,
      typeCheckingClassifierMembershipFields x = typeCheckingClassifierMembershipFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T₁ J₁ E₁ D₁ S₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ J₂ E₂ D₂ S₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance typeCheckingClassifierMembershipBHistCarrier :
    BHistCarrier TypeCheckingClassifierMembershipUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typeCheckingClassifierMembershipToEventFlow
  fromEventFlow := typeCheckingClassifierMembershipFromEventFlow

instance typeCheckingClassifierMembershipChapterTasteGate :
    ChapterTasteGate TypeCheckingClassifierMembershipUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      typeCheckingClassifierMembershipFromEventFlow
        (typeCheckingClassifierMembershipToEventFlow x) = some x
    exact typeCheckingClassifierMembership_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (typeCheckingClassifierMembershipToEventFlow_injective heq)

instance typeCheckingClassifierMembershipFieldFaithful :
    FieldFaithful TypeCheckingClassifierMembershipUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := typeCheckingClassifierMembershipFields
  field_faithful := typeCheckingClassifierMembership_field_faithful

instance typeCheckingClassifierMembershipNontrivial :
    Nontrivial TypeCheckingClassifierMembershipUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TypeCheckingClassifierMembershipUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TypeCheckingClassifierMembershipUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TypeCheckingClassifierMembershipUp :=
  -- BEDC touchpoint anchor: BHist BMark
  typeCheckingClassifierMembershipChapterTasteGate

end BEDC.Derived.TypeCheckingClassifierMembershipUp
