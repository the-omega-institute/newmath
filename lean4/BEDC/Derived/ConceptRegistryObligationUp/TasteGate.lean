import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConceptRegistryObligationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConceptRegistryObligationUp : Type where
  | mk (E A L F S X H C P N : BHist) : ConceptRegistryObligationUp
  deriving DecidableEq

def conceptRegistryObligationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: conceptRegistryObligationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: conceptRegistryObligationEncodeBHist h

def conceptRegistryObligationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (conceptRegistryObligationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (conceptRegistryObligationDecodeBHist tail)

private theorem conceptRegistryObligation_decode_encode_bhist :
    ∀ h : BHist,
      conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def conceptRegistryObligationFields : ConceptRegistryObligationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConceptRegistryObligationUp.mk E A L F S X H C P N => [E, A, L, F, S, X, H, C, P, N]

def conceptRegistryObligationToEventFlow : ConceptRegistryObligationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map conceptRegistryObligationEncodeBHist (conceptRegistryObligationFields x)

def conceptRegistryObligationFromEventFlow : EventFlow → Option ConceptRegistryObligationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | X :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ConceptRegistryObligationUp.mk
                                                  (conceptRegistryObligationDecodeBHist E)
                                                  (conceptRegistryObligationDecodeBHist A)
                                                  (conceptRegistryObligationDecodeBHist L)
                                                  (conceptRegistryObligationDecodeBHist F)
                                                  (conceptRegistryObligationDecodeBHist S)
                                                  (conceptRegistryObligationDecodeBHist X)
                                                  (conceptRegistryObligationDecodeBHist H)
                                                  (conceptRegistryObligationDecodeBHist C)
                                                  (conceptRegistryObligationDecodeBHist P)
                                                  (conceptRegistryObligationDecodeBHist N))
                                          | _ :: _ => none

private theorem conceptRegistryObligation_round_trip :
    ∀ x : ConceptRegistryObligationUp,
      conceptRegistryObligationFromEventFlow
          (conceptRegistryObligationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E A L F S X H C P N =>
      change
        some
          (ConceptRegistryObligationUp.mk
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist E))
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist A))
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist L))
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist F))
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist S))
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist X))
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist H))
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist C))
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist P))
            (conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist N))) =
          some (ConceptRegistryObligationUp.mk E A L F S X H C P N)
      rw [conceptRegistryObligation_decode_encode_bhist E,
        conceptRegistryObligation_decode_encode_bhist A,
        conceptRegistryObligation_decode_encode_bhist L,
        conceptRegistryObligation_decode_encode_bhist F,
        conceptRegistryObligation_decode_encode_bhist S,
        conceptRegistryObligation_decode_encode_bhist X,
        conceptRegistryObligation_decode_encode_bhist H,
        conceptRegistryObligation_decode_encode_bhist C,
        conceptRegistryObligation_decode_encode_bhist P,
        conceptRegistryObligation_decode_encode_bhist N]

private theorem conceptRegistryObligationToEventFlow_injective
    {x y : ConceptRegistryObligationUp} :
    conceptRegistryObligationToEventFlow x = conceptRegistryObligationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      conceptRegistryObligationFromEventFlow (conceptRegistryObligationToEventFlow x) =
        conceptRegistryObligationFromEventFlow (conceptRegistryObligationToEventFlow y) :=
    congrArg conceptRegistryObligationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (conceptRegistryObligation_round_trip x).symm
      (Eq.trans hread (conceptRegistryObligation_round_trip y)))

private theorem conceptRegistryObligation_field_faithful :
    ∀ x y : ConceptRegistryObligationUp,
      conceptRegistryObligationFields x = conceptRegistryObligationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk E₁ A₁ L₁ F₁ S₁ X₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ A₂ L₂ F₂ S₂ X₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance conceptRegistryObligationBHistCarrier :
    BHistCarrier ConceptRegistryObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := conceptRegistryObligationToEventFlow
  fromEventFlow := conceptRegistryObligationFromEventFlow

instance conceptRegistryObligationChapterTasteGate :
    ChapterTasteGate ConceptRegistryObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      conceptRegistryObligationFromEventFlow
        (conceptRegistryObligationToEventFlow x) = some x
    exact conceptRegistryObligation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (conceptRegistryObligationToEventFlow_injective heq)

instance conceptRegistryObligationFieldFaithful :
    FieldFaithful ConceptRegistryObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := conceptRegistryObligationFields
  field_faithful := conceptRegistryObligation_field_faithful

instance conceptRegistryObligationNontrivial : Nontrivial ConceptRegistryObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConceptRegistryObligationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConceptRegistryObligationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConceptRegistryObligationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  conceptRegistryObligationChapterTasteGate

theorem ConceptRegistryObligationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      conceptRegistryObligationDecodeBHist (conceptRegistryObligationEncodeBHist h) = h) ∧
      (∀ x : ConceptRegistryObligationUp,
        conceptRegistryObligationFromEventFlow
          (conceptRegistryObligationToEventFlow x) = some x) ∧
        (∀ x y : ConceptRegistryObligationUp,
          conceptRegistryObligationToEventFlow x =
            conceptRegistryObligationToEventFlow y → x = y) ∧
          conceptRegistryObligationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact conceptRegistryObligation_decode_encode_bhist
  · constructor
    · exact conceptRegistryObligation_round_trip
    · constructor
      · intro x y heq
        exact conceptRegistryObligationToEventFlow_injective heq
      · rfl

end BEDC.Derived.ConceptRegistryObligationUp
