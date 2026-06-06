import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductCompletionUp : Type where
  | mk
      (S0 S1 D0 D1 B R0 R1 L0 L1 E H C P N : BHist) :
      CauchyProductCompletionUp
  deriving DecidableEq

def cauchyProductCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductCompletionEncodeBHist h

def cauchyProductCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductCompletionDecodeBHist tail)

private theorem cauchyProductCompletionDecode_encode_bhist :
    ∀ h : BHist,
      cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyProductCompletionFields : CauchyProductCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductCompletionUp.mk S0 S1 D0 D1 B R0 R1 L0 L1 E H C P N =>
      [S0, S1, D0, D1, B, R0, R1, L0, L1, E, H, C, P, N]

def cauchyProductCompletionToEventFlow : CauchyProductCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductCompletionUp.mk S0 S1 D0 D1 B R0 R1 L0 L1 E H C P N =>
      [cauchyProductCompletionEncodeBHist S0,
        cauchyProductCompletionEncodeBHist S1,
        cauchyProductCompletionEncodeBHist D0,
        cauchyProductCompletionEncodeBHist D1,
        cauchyProductCompletionEncodeBHist B,
        cauchyProductCompletionEncodeBHist R0,
        cauchyProductCompletionEncodeBHist R1,
        cauchyProductCompletionEncodeBHist L0,
        cauchyProductCompletionEncodeBHist L1,
        cauchyProductCompletionEncodeBHist E,
        cauchyProductCompletionEncodeBHist H,
        cauchyProductCompletionEncodeBHist C,
        cauchyProductCompletionEncodeBHist P,
        cauchyProductCompletionEncodeBHist N]

def cauchyProductCompletionFromEventFlow : EventFlow → Option CauchyProductCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S0 :: rest0 =>
      match rest0 with
      | [] => none
      | S1 :: rest1 =>
          match rest1 with
          | [] => none
          | D0 :: rest2 =>
              match rest2 with
              | [] => none
              | D1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R0 :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R1 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L0 :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | L1 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | H :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | P :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | N :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (CauchyProductCompletionUp.mk
                                                                  (cauchyProductCompletionDecodeBHist S0)
                                                                  (cauchyProductCompletionDecodeBHist S1)
                                                                  (cauchyProductCompletionDecodeBHist D0)
                                                                  (cauchyProductCompletionDecodeBHist D1)
                                                                  (cauchyProductCompletionDecodeBHist B)
                                                                  (cauchyProductCompletionDecodeBHist R0)
                                                                  (cauchyProductCompletionDecodeBHist R1)
                                                                  (cauchyProductCompletionDecodeBHist L0)
                                                                  (cauchyProductCompletionDecodeBHist L1)
                                                                  (cauchyProductCompletionDecodeBHist E)
                                                                  (cauchyProductCompletionDecodeBHist H)
                                                                  (cauchyProductCompletionDecodeBHist C)
                                                                  (cauchyProductCompletionDecodeBHist P)
                                                                  (cauchyProductCompletionDecodeBHist N))
                                                          | _ :: _ => none

private theorem cauchyProductCompletion_round_trip :
    ∀ x : CauchyProductCompletionUp,
      cauchyProductCompletionFromEventFlow (cauchyProductCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 D0 D1 B R0 R1 L0 L1 E H C P N =>
      change
        some
            (CauchyProductCompletionUp.mk
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist S0))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist S1))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist D0))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist D1))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist B))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist R0))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist R1))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist L0))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist L1))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist E))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist H))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist C))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist P))
              (cauchyProductCompletionDecodeBHist (cauchyProductCompletionEncodeBHist N))) =
          some (CauchyProductCompletionUp.mk S0 S1 D0 D1 B R0 R1 L0 L1 E H C P N)
      rw [cauchyProductCompletionDecode_encode_bhist S0,
        cauchyProductCompletionDecode_encode_bhist S1,
        cauchyProductCompletionDecode_encode_bhist D0,
        cauchyProductCompletionDecode_encode_bhist D1,
        cauchyProductCompletionDecode_encode_bhist B,
        cauchyProductCompletionDecode_encode_bhist R0,
        cauchyProductCompletionDecode_encode_bhist R1,
        cauchyProductCompletionDecode_encode_bhist L0,
        cauchyProductCompletionDecode_encode_bhist L1,
        cauchyProductCompletionDecode_encode_bhist E,
        cauchyProductCompletionDecode_encode_bhist H,
        cauchyProductCompletionDecode_encode_bhist C,
        cauchyProductCompletionDecode_encode_bhist P,
        cauchyProductCompletionDecode_encode_bhist N]

private theorem cauchyProductCompletionToEventFlow_injective
    {x y : CauchyProductCompletionUp} :
    cauchyProductCompletionToEventFlow x = cauchyProductCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductCompletionFromEventFlow (cauchyProductCompletionToEventFlow x) =
        cauchyProductCompletionFromEventFlow (cauchyProductCompletionToEventFlow y) :=
    congrArg cauchyProductCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyProductCompletion_round_trip x).symm
      (Eq.trans hread (cauchyProductCompletion_round_trip y)))

instance cauchyProductCompletionBHistCarrier : BHistCarrier CauchyProductCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductCompletionToEventFlow
  fromEventFlow := cauchyProductCompletionFromEventFlow

instance cauchyProductCompletionChapterTasteGate :
    ChapterTasteGate CauchyProductCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyProductCompletionFromEventFlow (cauchyProductCompletionToEventFlow x) =
      some x
    exact cauchyProductCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyProductCompletionToEventFlow_injective heq)

instance cauchyProductCompletionFieldFaithful :
    FieldFaithful CauchyProductCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyProductCompletionFields
  field_faithful := by
    intro x y h
    cases x with
    | mk S0₁ S1₁ D0₁ D1₁ B₁ R0₁ R1₁ L0₁ L1₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk S0₂ S1₂ D0₂ D1₂ B₂ R0₂ R1₂ L0₂ L1₂ E₂ H₂ C₂ P₂ N₂ =>
            simp only [cauchyProductCompletionFields] at h
            cases h
            rfl

theorem CauchyProductCompletionTasteGate_single_carrier_alignment
    (x : CauchyProductCompletionUp) :
    (∃ S0 S1 D0 D1 B R0 R1 L0 L1 E H C P N : BHist,
      x = CauchyProductCompletionUp.mk S0 S1 D0 D1 B R0 R1 L0 L1 E H C P N ∧
        cauchyProductCompletionFields x =
          [S0, S1, D0, D1, B, R0, R1, L0, L1, E, H, C, P, N]) ∧
      cauchyProductCompletionFromEventFlow (cauchyProductCompletionToEventFlow x) =
        some x ∧
      cauchyProductCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  cases x with
  | mk S0 S1 D0 D1 B R0 R1 L0 L1 E H C P N =>
      exact
        ⟨⟨S0, S1, D0, D1, B, R0, R1, L0, L1, E, H, C, P, N, rfl, rfl⟩,
          cauchyProductCompletion_round_trip
            (CauchyProductCompletionUp.mk S0 S1 D0 D1 B R0 R1 L0 L1 E H C P N),
          rfl⟩

end BEDC.Derived.CauchyProductCompletionUp
