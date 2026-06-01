import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterCriterionUp : Type where
  | mk (B K M U W R D E H C P N : BHist) : CauchyFilterCriterionUp
  deriving DecidableEq

def cauchyFilterCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterCriterionEncodeBHist h

def cauchyFilterCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterCriterionDecodeBHist tail)

private theorem cauchyFilterCriterion_decode_encode_bhist :
    ∀ h : BHist, cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterCriterionFields : CauchyFilterCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterCriterionUp.mk B K M U W R D E H C P N => [B, K, M, U, W, R, D, E, H, C, P, N]

def cauchyFilterCriterionToEventFlow : CauchyFilterCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyFilterCriterionFields x).map cauchyFilterCriterionEncodeBHist

def cauchyFilterCriterionFromEventFlow : EventFlow → Option CauchyFilterCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | K :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | U :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (CauchyFilterCriterionUp.mk
                                                          (cauchyFilterCriterionDecodeBHist B)
                                                          (cauchyFilterCriterionDecodeBHist K)
                                                          (cauchyFilterCriterionDecodeBHist M)
                                                          (cauchyFilterCriterionDecodeBHist U)
                                                          (cauchyFilterCriterionDecodeBHist W)
                                                          (cauchyFilterCriterionDecodeBHist R)
                                                          (cauchyFilterCriterionDecodeBHist D)
                                                          (cauchyFilterCriterionDecodeBHist E)
                                                          (cauchyFilterCriterionDecodeBHist H)
                                                          (cauchyFilterCriterionDecodeBHist C)
                                                          (cauchyFilterCriterionDecodeBHist P)
                                                          (cauchyFilterCriterionDecodeBHist N))
                                                  | _ :: _ => none

private theorem cauchyFilterCriterion_round_trip :
    ∀ x : CauchyFilterCriterionUp,
      cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B K M U W R D E H C P N =>
      change
        some
          (CauchyFilterCriterionUp.mk
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist B))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist K))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist M))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist U))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist W))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist R))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist D))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist E))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist H))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist C))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist P))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist N))) =
          some (CauchyFilterCriterionUp.mk B K M U W R D E H C P N)
      rw [cauchyFilterCriterion_decode_encode_bhist B,
        cauchyFilterCriterion_decode_encode_bhist K,
        cauchyFilterCriterion_decode_encode_bhist M,
        cauchyFilterCriterion_decode_encode_bhist U,
        cauchyFilterCriterion_decode_encode_bhist W,
        cauchyFilterCriterion_decode_encode_bhist R,
        cauchyFilterCriterion_decode_encode_bhist D,
        cauchyFilterCriterion_decode_encode_bhist E,
        cauchyFilterCriterion_decode_encode_bhist H,
        cauchyFilterCriterion_decode_encode_bhist C,
        cauchyFilterCriterion_decode_encode_bhist P,
        cauchyFilterCriterion_decode_encode_bhist N]

private theorem cauchyFilterCriterionToEventFlow_injective
    {x y : CauchyFilterCriterionUp} :
    cauchyFilterCriterionToEventFlow x = cauchyFilterCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) =
        cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow y) :=
    congrArg cauchyFilterCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyFilterCriterion_round_trip x).symm
      (Eq.trans hread (cauchyFilterCriterion_round_trip y)))

private theorem cauchyFilterCriterion_field_faithful :
    ∀ x y : CauchyFilterCriterionUp,
      cauchyFilterCriterionFields x = cauchyFilterCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ K₁ M₁ U₁ W₁ R₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ K₂ M₂ U₂ W₂ R₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hB tail0
          injection tail0 with hK tail1
          injection tail1 with hM tail2
          injection tail2 with hU tail3
          injection tail3 with hW tail4
          injection tail4 with hR tail5
          injection tail5 with hD tail6
          injection tail6 with hE tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hB
          subst hK
          subst hM
          subst hU
          subst hW
          subst hR
          subst hD
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyFilterCriterionBHistCarrier : BHistCarrier CauchyFilterCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterCriterionToEventFlow
  fromEventFlow := cauchyFilterCriterionFromEventFlow

instance cauchyFilterCriterionChapterTasteGate : ChapterTasteGate CauchyFilterCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) = some x
    exact cauchyFilterCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyFilterCriterionToEventFlow_injective heq)

instance cauchyFilterCriterionFieldFaithful : FieldFaithful CauchyFilterCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyFilterCriterionFields
  field_faithful := cauchyFilterCriterion_field_faithful

instance cauchyFilterCriterionNontrivial : Nontrivial CauchyFilterCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyFilterCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyFilterCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyFilterCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterCriterionChapterTasteGate

theorem CauchyFilterCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist h) = h) ∧
      (∀ x : CauchyFilterCriterionUp,
        cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) = some x) ∧
        (∀ x y : CauchyFilterCriterionUp,
          cauchyFilterCriterionToEventFlow x = cauchyFilterCriterionToEventFlow y → x = y) ∧
          cauchyFilterCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨cauchyFilterCriterion_decode_encode_bhist, cauchyFilterCriterion_round_trip,
      (fun _ _ heq => cauchyFilterCriterionToEventFlow_injective heq), rfl⟩

end BEDC.Derived.CauchyFilterCriterionUp
