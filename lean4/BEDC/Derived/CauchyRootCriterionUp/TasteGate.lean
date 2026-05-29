import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRootCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRootCriterionUp : Type where
  | mk (A Q W D T R E H C P N : BHist) : CauchyRootCriterionUp
  deriving DecidableEq

def cauchyRootCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRootCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRootCriterionEncodeBHist h

def cauchyRootCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRootCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRootCriterionDecodeBHist tail)

private theorem cauchyRootCriterion_decode_encode_bhist :
    ∀ h : BHist, cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRootCriterionFields : CauchyRootCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRootCriterionUp.mk A Q W D T R E H C P N => [A, Q, W, D, T, R, E, H, C, P, N]

def cauchyRootCriterionToEventFlow : CauchyRootCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRootCriterionFields x).map cauchyRootCriterionEncodeBHist

def cauchyRootCriterionFromEventFlow : EventFlow → Option CauchyRootCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CauchyRootCriterionUp.mk
                                                      (cauchyRootCriterionDecodeBHist A)
                                                      (cauchyRootCriterionDecodeBHist Q)
                                                      (cauchyRootCriterionDecodeBHist W)
                                                      (cauchyRootCriterionDecodeBHist D)
                                                      (cauchyRootCriterionDecodeBHist T)
                                                      (cauchyRootCriterionDecodeBHist R)
                                                      (cauchyRootCriterionDecodeBHist E)
                                                      (cauchyRootCriterionDecodeBHist H)
                                                      (cauchyRootCriterionDecodeBHist C)
                                                      (cauchyRootCriterionDecodeBHist P)
                                                      (cauchyRootCriterionDecodeBHist N))
                                              | _ :: _ => none

private theorem cauchyRootCriterion_round_trip :
    ∀ x : CauchyRootCriterionUp,
      cauchyRootCriterionFromEventFlow (cauchyRootCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Q W D T R E H C P N =>
      change
        some
          (CauchyRootCriterionUp.mk
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist A))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist Q))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist W))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist D))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist T))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist R))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist E))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist H))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist C))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist P))
            (cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist N))) =
          some (CauchyRootCriterionUp.mk A Q W D T R E H C P N)
      rw [cauchyRootCriterion_decode_encode_bhist A,
        cauchyRootCriterion_decode_encode_bhist Q,
        cauchyRootCriterion_decode_encode_bhist W,
        cauchyRootCriterion_decode_encode_bhist D,
        cauchyRootCriterion_decode_encode_bhist T,
        cauchyRootCriterion_decode_encode_bhist R,
        cauchyRootCriterion_decode_encode_bhist E,
        cauchyRootCriterion_decode_encode_bhist H,
        cauchyRootCriterion_decode_encode_bhist C,
        cauchyRootCriterion_decode_encode_bhist P,
        cauchyRootCriterion_decode_encode_bhist N]

private theorem cauchyRootCriterionToEventFlow_injective {x y : CauchyRootCriterionUp} :
    cauchyRootCriterionToEventFlow x = cauchyRootCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRootCriterionFromEventFlow (cauchyRootCriterionToEventFlow x) =
        cauchyRootCriterionFromEventFlow (cauchyRootCriterionToEventFlow y) :=
    congrArg cauchyRootCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRootCriterion_round_trip x).symm
      (Eq.trans hread (cauchyRootCriterion_round_trip y)))

private theorem cauchyRootCriterion_field_faithful :
    ∀ x y : CauchyRootCriterionUp,
      cauchyRootCriterionFields x = cauchyRootCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ Q₁ W₁ D₁ T₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ Q₂ W₂ D₂ T₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hA tail0
          injection tail0 with hQ tail1
          injection tail1 with hW tail2
          injection tail2 with hD tail3
          injection tail3 with hT tail4
          injection tail4 with hR tail5
          injection tail5 with hE tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hA
          subst hQ
          subst hW
          subst hD
          subst hT
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyRootCriterionBHistCarrier : BHistCarrier CauchyRootCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRootCriterionToEventFlow
  fromEventFlow := cauchyRootCriterionFromEventFlow

instance cauchyRootCriterionChapterTasteGate : ChapterTasteGate CauchyRootCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRootCriterionFromEventFlow (cauchyRootCriterionToEventFlow x) = some x
    exact cauchyRootCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRootCriterionToEventFlow_injective heq)

instance cauchyRootCriterionFieldFaithful : FieldFaithful CauchyRootCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRootCriterionFields
  field_faithful := cauchyRootCriterion_field_faithful

instance cauchyRootCriterionNontrivial : Nontrivial CauchyRootCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRootCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRootCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRootCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRootCriterionChapterTasteGate

theorem CauchyRootCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRootCriterionDecodeBHist (cauchyRootCriterionEncodeBHist h) = h) ∧
      (∀ x : CauchyRootCriterionUp,
        cauchyRootCriterionFromEventFlow (cauchyRootCriterionToEventFlow x) = some x) ∧
        (∀ x y : CauchyRootCriterionUp,
          cauchyRootCriterionToEventFlow x = cauchyRootCriterionToEventFlow y → x = y) ∧
          cauchyRootCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨cauchyRootCriterion_decode_encode_bhist, cauchyRootCriterion_round_trip,
      (fun _ _ heq => cauchyRootCriterionToEventFlow_injective heq), rfl⟩

end BEDC.Derived.CauchyRootCriterionUp
