import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModelSelectionBoundaryUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModelSelectionBoundaryUp : Type where
  | mk (M S F D L T P N : BHist) : ModelSelectionBoundaryUp
  deriving DecidableEq

def modelSelectionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modelSelectionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modelSelectionBoundaryEncodeBHist h

def modelSelectionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modelSelectionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modelSelectionBoundaryDecodeBHist tail)

private theorem modelSelectionBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      modelSelectionBoundaryDecodeBHist (modelSelectionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modelSelectionBoundaryFields : ModelSelectionBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModelSelectionBoundaryUp.mk M S F D L T P N => [M, S, F, D, L, T, P, N]

def modelSelectionBoundaryToEventFlow : ModelSelectionBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ModelSelectionBoundaryUp.mk M S F D L T P N =>
      [[BMark.b0],
        modelSelectionBoundaryEncodeBHist M,
        [BMark.b1, BMark.b0],
        modelSelectionBoundaryEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        modelSelectionBoundaryEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelSelectionBoundaryEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelSelectionBoundaryEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelSelectionBoundaryEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelSelectionBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        modelSelectionBoundaryEncodeBHist N]

def modelSelectionBoundaryFromEventFlow : EventFlow → Option ModelSelectionBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | L :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | T :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ModelSelectionBoundaryUp.mk
                                                                          (modelSelectionBoundaryDecodeBHist M)
                                                                          (modelSelectionBoundaryDecodeBHist S)
                                                                          (modelSelectionBoundaryDecodeBHist F)
                                                                          (modelSelectionBoundaryDecodeBHist D)
                                                                          (modelSelectionBoundaryDecodeBHist L)
                                                                          (modelSelectionBoundaryDecodeBHist T)
                                                                          (modelSelectionBoundaryDecodeBHist P)
                                                                          (modelSelectionBoundaryDecodeBHist N))
                                                                  | _ :: _ => none

private theorem modelSelectionBoundary_round_trip :
    ∀ x : ModelSelectionBoundaryUp,
      modelSelectionBoundaryFromEventFlow (modelSelectionBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S F D L T P N =>
      change
        some
          (ModelSelectionBoundaryUp.mk
            (modelSelectionBoundaryDecodeBHist (modelSelectionBoundaryEncodeBHist M))
            (modelSelectionBoundaryDecodeBHist (modelSelectionBoundaryEncodeBHist S))
            (modelSelectionBoundaryDecodeBHist (modelSelectionBoundaryEncodeBHist F))
            (modelSelectionBoundaryDecodeBHist (modelSelectionBoundaryEncodeBHist D))
            (modelSelectionBoundaryDecodeBHist (modelSelectionBoundaryEncodeBHist L))
            (modelSelectionBoundaryDecodeBHist (modelSelectionBoundaryEncodeBHist T))
            (modelSelectionBoundaryDecodeBHist (modelSelectionBoundaryEncodeBHist P))
            (modelSelectionBoundaryDecodeBHist (modelSelectionBoundaryEncodeBHist N))) =
          some (ModelSelectionBoundaryUp.mk M S F D L T P N)
      rw [modelSelectionBoundaryDecode_encode_bhist M,
        modelSelectionBoundaryDecode_encode_bhist S,
        modelSelectionBoundaryDecode_encode_bhist F,
        modelSelectionBoundaryDecode_encode_bhist D,
        modelSelectionBoundaryDecode_encode_bhist L,
        modelSelectionBoundaryDecode_encode_bhist T,
        modelSelectionBoundaryDecode_encode_bhist P,
        modelSelectionBoundaryDecode_encode_bhist N]

private theorem modelSelectionBoundaryToEventFlow_injective {x y : ModelSelectionBoundaryUp} :
    modelSelectionBoundaryToEventFlow x = modelSelectionBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modelSelectionBoundaryFromEventFlow (modelSelectionBoundaryToEventFlow x) =
        modelSelectionBoundaryFromEventFlow (modelSelectionBoundaryToEventFlow y) :=
    congrArg modelSelectionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (modelSelectionBoundary_round_trip x).symm
      (Eq.trans hread (modelSelectionBoundary_round_trip y)))

private theorem modelSelectionBoundary_field_faithful :
    ∀ x y : ModelSelectionBoundaryUp,
      modelSelectionBoundaryFields x = modelSelectionBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk M₁ S₁ F₁ D₁ L₁ T₁ P₁ N₁ =>
      cases y with
      | mk M₂ S₂ F₂ D₂ L₂ T₂ P₂ N₂ =>
          cases h
          rfl

instance modelSelectionBoundaryBHistCarrier : BHistCarrier ModelSelectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modelSelectionBoundaryToEventFlow
  fromEventFlow := modelSelectionBoundaryFromEventFlow

instance modelSelectionBoundaryChapterTasteGate : ChapterTasteGate ModelSelectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change modelSelectionBoundaryFromEventFlow (modelSelectionBoundaryToEventFlow x) = some x
    exact modelSelectionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (modelSelectionBoundaryToEventFlow_injective heq)

instance modelSelectionBoundaryFieldFaithful : FieldFaithful ModelSelectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := modelSelectionBoundaryFields
  field_faithful := modelSelectionBoundary_field_faithful

instance modelSelectionBoundaryNontrivial : Nontrivial ModelSelectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ModelSelectionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ModelSelectionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ModelSelectionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modelSelectionBoundaryChapterTasteGate

theorem ModelSelectionBoundaryTasteGate_single_carrier_alignment :
    (∀ x : ModelSelectionBoundaryUp,
      modelSelectionBoundaryFromEventFlow (modelSelectionBoundaryToEventFlow x) = some x) ∧
      (∀ x y : ModelSelectionBoundaryUp,
        modelSelectionBoundaryToEventFlow x = modelSelectionBoundaryToEventFlow y → x = y) ∧
        (∀ (x : ModelSelectionBoundaryUp) w m,
          List.Mem w (modelSelectionBoundaryToEventFlow x) → List.Mem m w →
            m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact modelSelectionBoundary_round_trip
  · constructor
    · intro x y heq
      exact modelSelectionBoundaryToEventFlow_injective heq
    · intro _x _w _m hw hm
      exact event_flow_conservativity hw hm

theorem ModelSelectionBoundary_defeat_surface {M S F D L T P N : BHist} :
    modelSelectionBoundaryFields (ModelSelectionBoundaryUp.mk M S F D L T P N) =
        [M, S, F, D, L, T, P, N] ∧
      Cont M D (append M D) ∧
        Cont F L (append F L) ∧
          hsame T T ∧
            hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont
  constructor
  · rfl
  constructor
  · exact cont_intro rfl
  constructor
  · exact cont_intro rfl
  constructor
  · exact hsame_refl T
  · exact hsame_refl N

end BEDC.Derived.ModelSelectionBoundaryUp.TasteGate
