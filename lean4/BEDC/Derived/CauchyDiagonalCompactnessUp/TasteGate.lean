import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDiagonalCompactnessUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDiagonalCompactnessUp : Type where
  | mk : (B F W Q D E H C P N : BHist) → CauchyDiagonalCompactnessUp
  deriving DecidableEq

def cauchyDiagonalCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDiagonalCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDiagonalCompactnessEncodeBHist h

def cauchyDiagonalCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDiagonalCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDiagonalCompactnessDecodeBHist tail)

private theorem cauchyDiagonalCompactnessDecode_encode_bhist :
    ∀ h : BHist,
      cauchyDiagonalCompactnessDecodeBHist
        (cauchyDiagonalCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyDiagonalCompactnessFields : CauchyDiagonalCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDiagonalCompactnessUp.mk B F W Q D E H C P N => [B, F, W, Q, D, E, H, C, P, N]

def cauchyDiagonalCompactnessToEventFlow : CauchyDiagonalCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyDiagonalCompactnessFields x).map cauchyDiagonalCompactnessEncodeBHist

def cauchyDiagonalCompactnessFromEventFlow :
    EventFlow → Option CauchyDiagonalCompactnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                                (CauchyDiagonalCompactnessUp.mk
                                                  (cauchyDiagonalCompactnessDecodeBHist B)
                                                  (cauchyDiagonalCompactnessDecodeBHist F)
                                                  (cauchyDiagonalCompactnessDecodeBHist W)
                                                  (cauchyDiagonalCompactnessDecodeBHist Q)
                                                  (cauchyDiagonalCompactnessDecodeBHist D)
                                                  (cauchyDiagonalCompactnessDecodeBHist E)
                                                  (cauchyDiagonalCompactnessDecodeBHist H)
                                                  (cauchyDiagonalCompactnessDecodeBHist C)
                                                  (cauchyDiagonalCompactnessDecodeBHist P)
                                                  (cauchyDiagonalCompactnessDecodeBHist N))
                                          | _ :: _ => none

private theorem cauchyDiagonalCompactness_round_trip :
    ∀ x : CauchyDiagonalCompactnessUp,
      cauchyDiagonalCompactnessFromEventFlow
        (cauchyDiagonalCompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B F W Q D E H C P N =>
      change
        some
          (CauchyDiagonalCompactnessUp.mk
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist B))
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist F))
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist W))
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist Q))
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist D))
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist E))
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist H))
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist C))
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist P))
            (cauchyDiagonalCompactnessDecodeBHist
              (cauchyDiagonalCompactnessEncodeBHist N))) =
          some (CauchyDiagonalCompactnessUp.mk B F W Q D E H C P N)
      rw [cauchyDiagonalCompactnessDecode_encode_bhist B,
        cauchyDiagonalCompactnessDecode_encode_bhist F,
        cauchyDiagonalCompactnessDecode_encode_bhist W,
        cauchyDiagonalCompactnessDecode_encode_bhist Q,
        cauchyDiagonalCompactnessDecode_encode_bhist D,
        cauchyDiagonalCompactnessDecode_encode_bhist E,
        cauchyDiagonalCompactnessDecode_encode_bhist H,
        cauchyDiagonalCompactnessDecode_encode_bhist C,
        cauchyDiagonalCompactnessDecode_encode_bhist P,
        cauchyDiagonalCompactnessDecode_encode_bhist N]

private theorem cauchyDiagonalCompactnessToEventFlow_injective
    {x y : CauchyDiagonalCompactnessUp} :
    cauchyDiagonalCompactnessToEventFlow x =
      cauchyDiagonalCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDiagonalCompactnessFromEventFlow
          (cauchyDiagonalCompactnessToEventFlow x) =
        cauchyDiagonalCompactnessFromEventFlow
          (cauchyDiagonalCompactnessToEventFlow y) :=
    congrArg cauchyDiagonalCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyDiagonalCompactness_round_trip x).symm
      (Eq.trans hread (cauchyDiagonalCompactness_round_trip y)))

private theorem cauchyDiagonalCompactness_field_faithful :
    ∀ x y : CauchyDiagonalCompactnessUp,
      cauchyDiagonalCompactnessFields x = cauchyDiagonalCompactnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk B₁ F₁ W₁ Q₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ F₂ W₂ Q₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          injection h with hB hRest₁
          injection hRest₁ with hF hRest₂
          injection hRest₂ with hW hRest₃
          injection hRest₃ with hQ hRest₄
          injection hRest₄ with hD hRest₅
          injection hRest₅ with hE hRest₆
          injection hRest₆ with hH hRest₇
          injection hRest₇ with hC hRest₈
          injection hRest₈ with hP hRest₉
          injection hRest₉ with hN _
          subst hB
          subst hF
          subst hW
          subst hQ
          subst hD
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyDiagonalCompactnessBHistCarrier :
    BHistCarrier CauchyDiagonalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDiagonalCompactnessToEventFlow
  fromEventFlow := cauchyDiagonalCompactnessFromEventFlow

instance cauchyDiagonalCompactnessChapterTasteGate :
    ChapterTasteGate CauchyDiagonalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyDiagonalCompactnessFromEventFlow
        (cauchyDiagonalCompactnessToEventFlow x) = some x
    exact cauchyDiagonalCompactness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyDiagonalCompactnessToEventFlow_injective heq)

instance cauchyDiagonalCompactnessFieldFaithful :
    FieldFaithful CauchyDiagonalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyDiagonalCompactnessFields
  field_faithful := cauchyDiagonalCompactness_field_faithful

instance cauchyDiagonalCompactnessNontrivial :
    Nontrivial CauchyDiagonalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyDiagonalCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyDiagonalCompactnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyDiagonalCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyDiagonalCompactnessChapterTasteGate

theorem CauchyDiagonalCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cauchyDiagonalCompactnessDecodeBHist
          (cauchyDiagonalCompactnessEncodeBHist h) = h) ∧
      Nonempty (Nontrivial CauchyDiagonalCompactnessUp) ∧
        Nonempty (ChapterTasteGate CauchyDiagonalCompactnessUp) ∧
          Nonempty (FieldFaithful CauchyDiagonalCompactnessUp) ∧
            cauchyDiagonalCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyDiagonalCompactnessDecode_encode_bhist,
      ⟨⟨cauchyDiagonalCompactnessNontrivial⟩,
        ⟨⟨cauchyDiagonalCompactnessChapterTasteGate⟩,
          ⟨⟨cauchyDiagonalCompactnessFieldFaithful⟩, rfl⟩⟩⟩⟩

end TasteGate
end BEDC.Derived.CauchyDiagonalCompactnessUp
