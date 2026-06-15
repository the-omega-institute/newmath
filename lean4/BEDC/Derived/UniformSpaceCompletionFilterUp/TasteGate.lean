import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformSpaceCompletionFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformSpaceCompletionFilterUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk : (U B F S R D A H C P N : BHist) → UniformSpaceCompletionFilterUp
  deriving DecidableEq

def uniformSpaceCompletionFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformSpaceCompletionFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformSpaceCompletionFilterEncodeBHist h

def uniformSpaceCompletionFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformSpaceCompletionFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformSpaceCompletionFilterDecodeBHist tail)

private theorem uniformSpaceCompletionFilter_decode_encode_bhist :
    ∀ h : BHist,
      uniformSpaceCompletionFilterDecodeBHist
          (uniformSpaceCompletionFilterEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformSpaceCompletionFilterFields :
    UniformSpaceCompletionFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformSpaceCompletionFilterUp.mk U B F S R D A H C P N =>
      [U, B, F, S, R, D, A, H, C, P, N]

def uniformSpaceCompletionFilterToEventFlow :
    UniformSpaceCompletionFilterUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (uniformSpaceCompletionFilterFields x).map
      uniformSpaceCompletionFilterEncodeBHist

def uniformSpaceCompletionFilterFromEventFlow :
    EventFlow → Option UniformSpaceCompletionFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | F :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | A :: rest6 =>
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
                                                    (UniformSpaceCompletionFilterUp.mk
                                                      (uniformSpaceCompletionFilterDecodeBHist U)
                                                      (uniformSpaceCompletionFilterDecodeBHist B)
                                                      (uniformSpaceCompletionFilterDecodeBHist F)
                                                      (uniformSpaceCompletionFilterDecodeBHist S)
                                                      (uniformSpaceCompletionFilterDecodeBHist R)
                                                      (uniformSpaceCompletionFilterDecodeBHist D)
                                                      (uniformSpaceCompletionFilterDecodeBHist A)
                                                      (uniformSpaceCompletionFilterDecodeBHist H)
                                                      (uniformSpaceCompletionFilterDecodeBHist C)
                                                      (uniformSpaceCompletionFilterDecodeBHist P)
                                                      (uniformSpaceCompletionFilterDecodeBHist N))
                                              | _ :: _ => none

private theorem uniformSpaceCompletionFilter_round_trip :
    ∀ x : UniformSpaceCompletionFilterUp,
      uniformSpaceCompletionFilterFromEventFlow
          (uniformSpaceCompletionFilterToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U B F S R D A H C P N =>
      change
        some
          (UniformSpaceCompletionFilterUp.mk
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist U))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist B))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist F))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist S))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist R))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist D))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist A))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist H))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist C))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist P))
            (uniformSpaceCompletionFilterDecodeBHist
              (uniformSpaceCompletionFilterEncodeBHist N))) =
          some (UniformSpaceCompletionFilterUp.mk U B F S R D A H C P N)
      rw [uniformSpaceCompletionFilter_decode_encode_bhist U,
        uniformSpaceCompletionFilter_decode_encode_bhist B,
        uniformSpaceCompletionFilter_decode_encode_bhist F,
        uniformSpaceCompletionFilter_decode_encode_bhist S,
        uniformSpaceCompletionFilter_decode_encode_bhist R,
        uniformSpaceCompletionFilter_decode_encode_bhist D,
        uniformSpaceCompletionFilter_decode_encode_bhist A,
        uniformSpaceCompletionFilter_decode_encode_bhist H,
        uniformSpaceCompletionFilter_decode_encode_bhist C,
        uniformSpaceCompletionFilter_decode_encode_bhist P,
        uniformSpaceCompletionFilter_decode_encode_bhist N]

private theorem uniformSpaceCompletionFilterToEventFlow_injective
    {x y : UniformSpaceCompletionFilterUp} :
    uniformSpaceCompletionFilterToEventFlow x =
        uniformSpaceCompletionFilterToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      uniformSpaceCompletionFilterFromEventFlow
          (uniformSpaceCompletionFilterToEventFlow x) =
        uniformSpaceCompletionFilterFromEventFlow
          (uniformSpaceCompletionFilterToEventFlow y) :=
    congrArg uniformSpaceCompletionFilterFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (uniformSpaceCompletionFilter_round_trip x).symm
      (Eq.trans hread (uniformSpaceCompletionFilter_round_trip y)))

private theorem uniformSpaceCompletionFilter_field_faithful :
    ∀ x y : UniformSpaceCompletionFilterUp,
      uniformSpaceCompletionFilterFields x =
          uniformSpaceCompletionFilterFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ B₁ F₁ S₁ R₁ D₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ B₂ F₂ S₂ R₂ D₂ A₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hU tail1
          injection tail1 with hB tail2
          injection tail2 with hF tail3
          injection tail3 with hS tail4
          injection tail4 with hR tail5
          injection tail5 with hD tail6
          injection tail6 with hA tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          cases hU
          cases hB
          cases hF
          cases hS
          cases hR
          cases hD
          cases hA
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance uniformSpaceCompletionFilterBHistCarrier :
    BHistCarrier UniformSpaceCompletionFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformSpaceCompletionFilterToEventFlow
  fromEventFlow := uniformSpaceCompletionFilterFromEventFlow

instance uniformSpaceCompletionFilterChapterTasteGate :
    ChapterTasteGate UniformSpaceCompletionFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformSpaceCompletionFilterFromEventFlow
          (uniformSpaceCompletionFilterToEventFlow x) =
        some x
    exact uniformSpaceCompletionFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformSpaceCompletionFilterToEventFlow_injective heq)

instance uniformSpaceCompletionFilterFieldFaithful :
    FieldFaithful UniformSpaceCompletionFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformSpaceCompletionFilterFields
  field_faithful := uniformSpaceCompletionFilter_field_faithful

instance uniformSpaceCompletionFilterNontrivial :
    Nontrivial UniformSpaceCompletionFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformSpaceCompletionFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      UniformSpaceCompletionFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hU
        cases hU⟩

def taste_gate : ChapterTasteGate UniformSpaceCompletionFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformSpaceCompletionFilterChapterTasteGate

def taste_gate_witness : FieldFaithful UniformSpaceCompletionFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformSpaceCompletionFilterFieldFaithful

theorem UniformSpaceCompletionFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformSpaceCompletionFilterDecodeBHist
          (uniformSpaceCompletionFilterEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier UniformSpaceCompletionFilterUp) ∧
        Nonempty (ChapterTasteGate UniformSpaceCompletionFilterUp) ∧
          uniformSpaceCompletionFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨uniformSpaceCompletionFilter_decode_encode_bhist,
      ⟨uniformSpaceCompletionFilterBHistCarrier⟩,
      ⟨uniformSpaceCompletionFilterChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.UniformSpaceCompletionFilterUp
