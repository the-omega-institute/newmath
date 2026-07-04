import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSequentialCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSequentialCriterionUp : Type where
  | mk (X W R D L K E H C P N : BHist) : RealSequentialCriterionUp
  deriving DecidableEq

def realSequentialCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSequentialCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSequentialCriterionEncodeBHist h

def realSequentialCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSequentialCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSequentialCriterionDecodeBHist tail)

private theorem realSequentialCriterion_decode_encode_bhist :
    ∀ h : BHist,
      realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realSequentialCriterionFields : RealSequentialCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSequentialCriterionUp.mk X W R D L K E H C P N =>
      [X, W, R, D, L, K, E, H, C, P, N]

def realSequentialCriterionToEventFlow : RealSequentialCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realSequentialCriterionEncodeBHist (realSequentialCriterionFields x)

def realSequentialCriterionFromEventFlow : EventFlow → Option RealSequentialCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
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
                                                    (RealSequentialCriterionUp.mk
                                                      (realSequentialCriterionDecodeBHist X)
                                                      (realSequentialCriterionDecodeBHist W)
                                                      (realSequentialCriterionDecodeBHist R)
                                                      (realSequentialCriterionDecodeBHist D)
                                                      (realSequentialCriterionDecodeBHist L)
                                                      (realSequentialCriterionDecodeBHist K)
                                                      (realSequentialCriterionDecodeBHist E)
                                                      (realSequentialCriterionDecodeBHist H)
                                                      (realSequentialCriterionDecodeBHist C)
                                                      (realSequentialCriterionDecodeBHist P)
                                                      (realSequentialCriterionDecodeBHist N))
                                              | _ :: _ => none

private theorem realSequentialCriterion_round_trip :
    ∀ x : RealSequentialCriterionUp,
      realSequentialCriterionFromEventFlow (realSequentialCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X W R D L K E H C P N =>
      change
        some
          (RealSequentialCriterionUp.mk
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist X))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist W))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist R))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist D))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist L))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist K))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist E))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist H))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist C))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist P))
            (realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist N))) =
          some (RealSequentialCriterionUp.mk X W R D L K E H C P N)
      rw [realSequentialCriterion_decode_encode_bhist X,
        realSequentialCriterion_decode_encode_bhist W,
        realSequentialCriterion_decode_encode_bhist R,
        realSequentialCriterion_decode_encode_bhist D,
        realSequentialCriterion_decode_encode_bhist L,
        realSequentialCriterion_decode_encode_bhist K,
        realSequentialCriterion_decode_encode_bhist E,
        realSequentialCriterion_decode_encode_bhist H,
        realSequentialCriterion_decode_encode_bhist C,
        realSequentialCriterion_decode_encode_bhist P,
        realSequentialCriterion_decode_encode_bhist N]

private theorem realSequentialCriterionToEventFlow_injective
    {x y : RealSequentialCriterionUp} :
    realSequentialCriterionToEventFlow x = realSequentialCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSequentialCriterionFromEventFlow (realSequentialCriterionToEventFlow x) =
        realSequentialCriterionFromEventFlow (realSequentialCriterionToEventFlow y) :=
    congrArg realSequentialCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realSequentialCriterion_round_trip x).symm
      (Eq.trans hread (realSequentialCriterion_round_trip y)))

private theorem realSequentialCriterion_field_faithful :
    ∀ x y : RealSequentialCriterionUp,
      realSequentialCriterionFields x = realSequentialCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X₁ W₁ R₁ D₁ L₁ K₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ W₂ R₂ D₂ L₂ K₂ E₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance realSequentialCriterionBHistCarrier : BHistCarrier RealSequentialCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSequentialCriterionToEventFlow
  fromEventFlow := realSequentialCriterionFromEventFlow

instance realSequentialCriterionChapterTasteGate :
    ChapterTasteGate RealSequentialCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSequentialCriterionFromEventFlow (realSequentialCriterionToEventFlow x) =
      some x
    exact realSequentialCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSequentialCriterionToEventFlow_injective heq)

instance realSequentialCriterionFieldFaithful : FieldFaithful RealSequentialCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realSequentialCriterionFields
  field_faithful := realSequentialCriterion_field_faithful

instance realSequentialCriterionNontrivial : Nontrivial RealSequentialCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSequentialCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealSequentialCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def realSequentialCriterion_taste_gate : ChapterTasteGate RealSequentialCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realSequentialCriterionChapterTasteGate

theorem RealSequentialCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realSequentialCriterionDecodeBHist (realSequentialCriterionEncodeBHist h) = h) ∧
      (∀ x : RealSequentialCriterionUp,
        realSequentialCriterionFromEventFlow (realSequentialCriterionToEventFlow x) =
          some x) ∧
      (∀ x y : RealSequentialCriterionUp,
        realSequentialCriterionToEventFlow x = realSequentialCriterionToEventFlow y →
          x = y) ∧
      realSequentialCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realSequentialCriterion_decode_encode_bhist,
      realSequentialCriterion_round_trip,
      fun _ _ heq => realSequentialCriterionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RealSequentialCriterionUp
