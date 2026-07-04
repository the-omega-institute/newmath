import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTwoEpsilonStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTwoEpsilonStabilityUp : Type where
  | mk (T B W0 W1 R S L H C P N : BHist) : RegularCauchyTwoEpsilonStabilityUp
  deriving DecidableEq

def regularCauchyTwoEpsilonStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTwoEpsilonStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTwoEpsilonStabilityEncodeBHist h

def regularCauchyTwoEpsilonStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTwoEpsilonStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTwoEpsilonStabilityDecodeBHist tail)

private theorem regularCauchyTwoEpsilonStability_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTwoEpsilonStabilityDecodeBHist
        (regularCauchyTwoEpsilonStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTwoEpsilonStabilityFields :
    RegularCauchyTwoEpsilonStabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTwoEpsilonStabilityUp.mk T B W0 W1 R S L H C P N =>
      [T, B, W0, W1, R, S, L, H, C, P, N]

def regularCauchyTwoEpsilonStabilityToEventFlow :
    RegularCauchyTwoEpsilonStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchyTwoEpsilonStabilityEncodeBHist
        (regularCauchyTwoEpsilonStabilityFields x)

def regularCauchyTwoEpsilonStabilityFromEventFlow :
    EventFlow → Option RegularCauchyTwoEpsilonStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | W0 :: rest2 =>
              match rest2 with
              | [] => none
              | W1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | L :: rest6 =>
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
                                                    (RegularCauchyTwoEpsilonStabilityUp.mk
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist T)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist B)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist W0)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist W1)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist R)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist S)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist L)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist H)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist C)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist P)
                                                      (regularCauchyTwoEpsilonStabilityDecodeBHist N))
                                              | _ :: _ => none

private theorem regularCauchyTwoEpsilonStability_round_trip :
    ∀ x : RegularCauchyTwoEpsilonStabilityUp,
      regularCauchyTwoEpsilonStabilityFromEventFlow
        (regularCauchyTwoEpsilonStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T B W0 W1 R S L H C P N =>
      change
        some
          (RegularCauchyTwoEpsilonStabilityUp.mk
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist T))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist B))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist W0))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist W1))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist R))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist S))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist L))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist H))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist C))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist P))
            (regularCauchyTwoEpsilonStabilityDecodeBHist
              (regularCauchyTwoEpsilonStabilityEncodeBHist N))) =
          some (RegularCauchyTwoEpsilonStabilityUp.mk T B W0 W1 R S L H C P N)
      rw [regularCauchyTwoEpsilonStability_decode_encode_bhist T,
        regularCauchyTwoEpsilonStability_decode_encode_bhist B,
        regularCauchyTwoEpsilonStability_decode_encode_bhist W0,
        regularCauchyTwoEpsilonStability_decode_encode_bhist W1,
        regularCauchyTwoEpsilonStability_decode_encode_bhist R,
        regularCauchyTwoEpsilonStability_decode_encode_bhist S,
        regularCauchyTwoEpsilonStability_decode_encode_bhist L,
        regularCauchyTwoEpsilonStability_decode_encode_bhist H,
        regularCauchyTwoEpsilonStability_decode_encode_bhist C,
        regularCauchyTwoEpsilonStability_decode_encode_bhist P,
        regularCauchyTwoEpsilonStability_decode_encode_bhist N]

private theorem regularCauchyTwoEpsilonStabilityToEventFlow_injective
    {x y : RegularCauchyTwoEpsilonStabilityUp} :
    regularCauchyTwoEpsilonStabilityToEventFlow x =
        regularCauchyTwoEpsilonStabilityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTwoEpsilonStabilityFromEventFlow
          (regularCauchyTwoEpsilonStabilityToEventFlow x) =
        regularCauchyTwoEpsilonStabilityFromEventFlow
          (regularCauchyTwoEpsilonStabilityToEventFlow y) :=
    congrArg regularCauchyTwoEpsilonStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTwoEpsilonStability_round_trip x).symm
      (Eq.trans hread (regularCauchyTwoEpsilonStability_round_trip y)))

private theorem regularCauchyTwoEpsilonStability_field_faithful :
    ∀ x y : RegularCauchyTwoEpsilonStabilityUp,
      regularCauchyTwoEpsilonStabilityFields x =
          regularCauchyTwoEpsilonStabilityFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T₁ B₁ W0₁ W1₁ R₁ S₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ B₂ W0₂ W1₂ R₂ S₂ L₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance regularCauchyTwoEpsilonStabilityBHistCarrier :
    BHistCarrier RegularCauchyTwoEpsilonStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTwoEpsilonStabilityToEventFlow
  fromEventFlow := regularCauchyTwoEpsilonStabilityFromEventFlow

instance regularCauchyTwoEpsilonStabilityChapterTasteGate :
    ChapterTasteGate RegularCauchyTwoEpsilonStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTwoEpsilonStabilityFromEventFlow
        (regularCauchyTwoEpsilonStabilityToEventFlow x) = some x
    exact regularCauchyTwoEpsilonStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTwoEpsilonStabilityToEventFlow_injective heq)

instance regularCauchyTwoEpsilonStabilityFieldFaithful :
    FieldFaithful RegularCauchyTwoEpsilonStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTwoEpsilonStabilityFields
  field_faithful := regularCauchyTwoEpsilonStability_field_faithful

instance regularCauchyTwoEpsilonStabilityNontrivial :
    Nontrivial RegularCauchyTwoEpsilonStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTwoEpsilonStabilityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyTwoEpsilonStabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def regularCauchyTwoEpsilonStability_taste_gate :
    ChapterTasteGate RegularCauchyTwoEpsilonStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTwoEpsilonStabilityChapterTasteGate

theorem RegularCauchyTwoEpsilonStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTwoEpsilonStabilityDecodeBHist
        (regularCauchyTwoEpsilonStabilityEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTwoEpsilonStabilityUp,
        regularCauchyTwoEpsilonStabilityFromEventFlow
          (regularCauchyTwoEpsilonStabilityToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyTwoEpsilonStabilityUp,
        regularCauchyTwoEpsilonStabilityToEventFlow x =
            regularCauchyTwoEpsilonStabilityToEventFlow y →
          x = y) ∧
      regularCauchyTwoEpsilonStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyTwoEpsilonStability_decode_encode_bhist,
      regularCauchyTwoEpsilonStability_round_trip,
      fun _ _ heq => regularCauchyTwoEpsilonStabilityToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyTwoEpsilonStabilityUp
