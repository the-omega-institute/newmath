import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ResearchProgrammeExecutionGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ResearchProgrammeExecutionGateUp : Type where
  | mk : (T P D S F B R H C Q N : BHist) → ResearchProgrammeExecutionGateUp
  deriving DecidableEq

def researchProgrammeExecutionGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: researchProgrammeExecutionGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: researchProgrammeExecutionGateEncodeBHist h

def researchProgrammeExecutionGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (researchProgrammeExecutionGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (researchProgrammeExecutionGateDecodeBHist tail)

private theorem researchProgrammeExecutionGateDecode_encode_bhist :
    ∀ h : BHist,
      researchProgrammeExecutionGateDecodeBHist
        (researchProgrammeExecutionGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def researchProgrammeExecutionGateFields :
    ResearchProgrammeExecutionGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ResearchProgrammeExecutionGateUp.mk T P D S F B R H C Q N =>
      [T, P, D, S, F, B, R, H, C, Q, N]

def researchProgrammeExecutionGateToEventFlow :
    ResearchProgrammeExecutionGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (researchProgrammeExecutionGateFields x).map
      researchProgrammeExecutionGateEncodeBHist

def researchProgrammeExecutionGateFromEventFlow :
    EventFlow → Option ResearchProgrammeExecutionGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest0 =>
      match rest0 with
      | [] => none
      | P :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | F :: rest4 =>
                      match rest4 with
                      | [] => none
                      | B :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | Q :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (ResearchProgrammeExecutionGateUp.mk
                                                      (researchProgrammeExecutionGateDecodeBHist T)
                                                      (researchProgrammeExecutionGateDecodeBHist P)
                                                      (researchProgrammeExecutionGateDecodeBHist D)
                                                      (researchProgrammeExecutionGateDecodeBHist S)
                                                      (researchProgrammeExecutionGateDecodeBHist F)
                                                      (researchProgrammeExecutionGateDecodeBHist B)
                                                      (researchProgrammeExecutionGateDecodeBHist R)
                                                      (researchProgrammeExecutionGateDecodeBHist H)
                                                      (researchProgrammeExecutionGateDecodeBHist C)
                                                      (researchProgrammeExecutionGateDecodeBHist Q)
                                                      (researchProgrammeExecutionGateDecodeBHist N))
                                              | _ :: _ => none

private theorem researchProgrammeExecutionGate_round_trip :
    ∀ x : ResearchProgrammeExecutionGateUp,
      researchProgrammeExecutionGateFromEventFlow
        (researchProgrammeExecutionGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T P D S F B R H C Q N =>
      change
        some
          (ResearchProgrammeExecutionGateUp.mk
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist T))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist P))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist D))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist S))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist F))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist B))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist R))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist H))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist C))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist Q))
            (researchProgrammeExecutionGateDecodeBHist
              (researchProgrammeExecutionGateEncodeBHist N))) =
          some (ResearchProgrammeExecutionGateUp.mk T P D S F B R H C Q N)
      rw [researchProgrammeExecutionGateDecode_encode_bhist T,
        researchProgrammeExecutionGateDecode_encode_bhist P,
        researchProgrammeExecutionGateDecode_encode_bhist D,
        researchProgrammeExecutionGateDecode_encode_bhist S,
        researchProgrammeExecutionGateDecode_encode_bhist F,
        researchProgrammeExecutionGateDecode_encode_bhist B,
        researchProgrammeExecutionGateDecode_encode_bhist R,
        researchProgrammeExecutionGateDecode_encode_bhist H,
        researchProgrammeExecutionGateDecode_encode_bhist C,
        researchProgrammeExecutionGateDecode_encode_bhist Q,
        researchProgrammeExecutionGateDecode_encode_bhist N]

private theorem researchProgrammeExecutionGateToEventFlow_injective
    {x y : ResearchProgrammeExecutionGateUp} :
    researchProgrammeExecutionGateToEventFlow x =
      researchProgrammeExecutionGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      researchProgrammeExecutionGateFromEventFlow
          (researchProgrammeExecutionGateToEventFlow x) =
        researchProgrammeExecutionGateFromEventFlow
          (researchProgrammeExecutionGateToEventFlow y) :=
    congrArg researchProgrammeExecutionGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (researchProgrammeExecutionGate_round_trip x).symm
      (Eq.trans hread (researchProgrammeExecutionGate_round_trip y)))

instance researchProgrammeExecutionGateBHistCarrier :
    BHistCarrier ResearchProgrammeExecutionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := researchProgrammeExecutionGateToEventFlow
  fromEventFlow := researchProgrammeExecutionGateFromEventFlow

instance researchProgrammeExecutionGateChapterTasteGate :
    ChapterTasteGate ResearchProgrammeExecutionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      researchProgrammeExecutionGateFromEventFlow
        (researchProgrammeExecutionGateToEventFlow x) = some x
    exact researchProgrammeExecutionGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (researchProgrammeExecutionGateToEventFlow_injective heq)

instance researchProgrammeExecutionGateFieldFaithful :
    FieldFaithful ResearchProgrammeExecutionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := researchProgrammeExecutionGateFields
  field_faithful := by
    intro x y h
    cases x with
    | mk T₁ P₁ D₁ S₁ F₁ B₁ R₁ H₁ C₁ Q₁ N₁ =>
        cases y with
        | mk T₂ P₂ D₂ S₂ F₂ B₂ R₂ H₂ C₂ Q₂ N₂ =>
            cases h
            rfl

instance researchProgrammeExecutionGateNontrivial :
    Nontrivial ResearchProgrammeExecutionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ResearchProgrammeExecutionGateUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ResearchProgrammeExecutionGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ResearchProgrammeExecutionGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  researchProgrammeExecutionGateChapterTasteGate

theorem ResearchProgrammeExecutionGateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      researchProgrammeExecutionGateDecodeBHist
        (researchProgrammeExecutionGateEncodeBHist h) = h) ∧
      (∀ x : ResearchProgrammeExecutionGateUp,
        researchProgrammeExecutionGateFromEventFlow
          (researchProgrammeExecutionGateToEventFlow x) = some x) ∧
      (∀ x y : ResearchProgrammeExecutionGateUp,
        researchProgrammeExecutionGateToEventFlow x =
          researchProgrammeExecutionGateToEventFlow y → x = y) ∧
      Nonempty (FieldFaithful ResearchProgrammeExecutionGateUp) ∧
        researchProgrammeExecutionGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact researchProgrammeExecutionGateDecode_encode_bhist
  · constructor
    · exact researchProgrammeExecutionGate_round_trip
    · constructor
      · exact fun _x _y => researchProgrammeExecutionGateToEventFlow_injective
      · constructor
        · exact
            ⟨{
              fields := researchProgrammeExecutionGateFields
              field_faithful := by
                intro x y h
                cases x with
                | mk T₁ P₁ D₁ S₁ F₁ B₁ R₁ H₁ C₁ Q₁ N₁ =>
                    cases y with
                    | mk T₂ P₂ D₂ S₂ F₂ B₂ R₂ H₂ C₂ Q₂ N₂ =>
                        injection h with hT hRest₁
                        injection hRest₁ with hP hRest₂
                        injection hRest₂ with hD hRest₃
                        injection hRest₃ with hS hRest₄
                        injection hRest₄ with hF hRest₅
                        injection hRest₅ with hB hRest₆
                        injection hRest₆ with hR hRest₇
                        injection hRest₇ with hH hRest₈
                        injection hRest₈ with hC hRest₉
                        injection hRest₉ with hQ hRest₁₀
                        injection hRest₁₀ with hN _
                        subst hT
                        subst hP
                        subst hD
                        subst hS
                        subst hF
                        subst hB
                        subst hR
                        subst hH
                        subst hC
                        subst hQ
                        subst hN
                        rfl
            }⟩
        · rfl

end BEDC.Derived.ResearchProgrammeExecutionGateUp
