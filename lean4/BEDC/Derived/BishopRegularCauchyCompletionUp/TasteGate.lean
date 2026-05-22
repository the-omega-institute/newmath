import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularCauchyCompletionUp : Type where
  | mk : (E S R D W H C P N : BHist) → BishopRegularCauchyCompletionUp
  deriving DecidableEq

def bishopRegularCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularCauchyCompletionEncodeBHist h

def bishopRegularCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularCauchyCompletionDecodeBHist tail)

private theorem bishopRegularCauchyCompletionDecode_encode_bhist :
    ∀ h : BHist,
      bishopRegularCauchyCompletionDecodeBHist
        (bishopRegularCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopRegularCauchyCompletionToEventFlow :
    BishopRegularCauchyCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularCauchyCompletionUp.mk E S R D W H C P N =>
      [bishopRegularCauchyCompletionEncodeBHist E,
        bishopRegularCauchyCompletionEncodeBHist S,
        bishopRegularCauchyCompletionEncodeBHist R,
        bishopRegularCauchyCompletionEncodeBHist D,
        bishopRegularCauchyCompletionEncodeBHist W,
        bishopRegularCauchyCompletionEncodeBHist H,
        bishopRegularCauchyCompletionEncodeBHist C,
        bishopRegularCauchyCompletionEncodeBHist P,
        bishopRegularCauchyCompletionEncodeBHist N]

def bishopRegularCauchyCompletionFromEventFlow :
    EventFlow → Option BishopRegularCauchyCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (BishopRegularCauchyCompletionUp.mk
                                              (bishopRegularCauchyCompletionDecodeBHist E)
                                              (bishopRegularCauchyCompletionDecodeBHist S)
                                              (bishopRegularCauchyCompletionDecodeBHist R)
                                              (bishopRegularCauchyCompletionDecodeBHist D)
                                              (bishopRegularCauchyCompletionDecodeBHist W)
                                              (bishopRegularCauchyCompletionDecodeBHist H)
                                              (bishopRegularCauchyCompletionDecodeBHist C)
                                              (bishopRegularCauchyCompletionDecodeBHist P)
                                              (bishopRegularCauchyCompletionDecodeBHist N))
                                      | _ :: _ => none

def bishopRegularCauchyCompletionFields :
    BishopRegularCauchyCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularCauchyCompletionUp.mk E S R D W H C P N => [E, S, R, D, W, H, C, P, N]

private theorem bishopRegularCauchyCompletion_round_trip :
    ∀ x : BishopRegularCauchyCompletionUp,
      bishopRegularCauchyCompletionFromEventFlow
        (bishopRegularCauchyCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E S R D W H C P N =>
      change
        some
          (BishopRegularCauchyCompletionUp.mk
            (bishopRegularCauchyCompletionDecodeBHist
              (bishopRegularCauchyCompletionEncodeBHist E))
            (bishopRegularCauchyCompletionDecodeBHist
              (bishopRegularCauchyCompletionEncodeBHist S))
            (bishopRegularCauchyCompletionDecodeBHist
              (bishopRegularCauchyCompletionEncodeBHist R))
            (bishopRegularCauchyCompletionDecodeBHist
              (bishopRegularCauchyCompletionEncodeBHist D))
            (bishopRegularCauchyCompletionDecodeBHist
              (bishopRegularCauchyCompletionEncodeBHist W))
            (bishopRegularCauchyCompletionDecodeBHist
              (bishopRegularCauchyCompletionEncodeBHist H))
            (bishopRegularCauchyCompletionDecodeBHist
              (bishopRegularCauchyCompletionEncodeBHist C))
            (bishopRegularCauchyCompletionDecodeBHist
              (bishopRegularCauchyCompletionEncodeBHist P))
            (bishopRegularCauchyCompletionDecodeBHist
              (bishopRegularCauchyCompletionEncodeBHist N))) =
          some (BishopRegularCauchyCompletionUp.mk E S R D W H C P N)
      rw [bishopRegularCauchyCompletionDecode_encode_bhist E,
        bishopRegularCauchyCompletionDecode_encode_bhist S,
        bishopRegularCauchyCompletionDecode_encode_bhist R,
        bishopRegularCauchyCompletionDecode_encode_bhist D,
        bishopRegularCauchyCompletionDecode_encode_bhist W,
        bishopRegularCauchyCompletionDecode_encode_bhist H,
        bishopRegularCauchyCompletionDecode_encode_bhist C,
        bishopRegularCauchyCompletionDecode_encode_bhist P,
        bishopRegularCauchyCompletionDecode_encode_bhist N]

private theorem bishopRegularCauchyCompletionToEventFlow_injective
    {x y : BishopRegularCauchyCompletionUp} :
    bishopRegularCauchyCompletionToEventFlow x =
      bishopRegularCauchyCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularCauchyCompletionFromEventFlow
          (bishopRegularCauchyCompletionToEventFlow x) =
        bishopRegularCauchyCompletionFromEventFlow
          (bishopRegularCauchyCompletionToEventFlow y) :=
    congrArg bishopRegularCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopRegularCauchyCompletion_round_trip x).symm
      (Eq.trans hread (bishopRegularCauchyCompletion_round_trip y)))

instance bishopRegularCauchyCompletionBHistCarrier :
    BHistCarrier BishopRegularCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularCauchyCompletionToEventFlow
  fromEventFlow := bishopRegularCauchyCompletionFromEventFlow

instance bishopRegularCauchyCompletionChapterTasteGate :
    ChapterTasteGate BishopRegularCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRegularCauchyCompletionFromEventFlow
        (bishopRegularCauchyCompletionToEventFlow x) = some x
    exact bishopRegularCauchyCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRegularCauchyCompletionToEventFlow_injective heq)

instance bishopRegularCauchyCompletionFieldFaithful :
    FieldFaithful BishopRegularCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRegularCauchyCompletionFields
  field_faithful := by
    intro x y h
    cases x with
    | mk E₁ S₁ R₁ D₁ W₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk E₂ S₂ R₂ D₂ W₂ H₂ C₂ P₂ N₂ =>
            cases h
            rfl

instance bishopRegularCauchyCompletionNontrivial :
    Nontrivial BishopRegularCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopRegularCauchyCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopRegularCauchyCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopRegularCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopRegularCauchyCompletionChapterTasteGate

theorem BishopRegularCauchyCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopRegularCauchyCompletionDecodeBHist
        (bishopRegularCauchyCompletionEncodeBHist h) = h) ∧
      (∀ x : BishopRegularCauchyCompletionUp,
        bishopRegularCauchyCompletionFromEventFlow
          (bishopRegularCauchyCompletionToEventFlow x) = some x) ∧
        (∀ x y : BishopRegularCauchyCompletionUp,
          bishopRegularCauchyCompletionToEventFlow x =
            bishopRegularCauchyCompletionToEventFlow y → x = y) ∧
          bishopRegularCauchyCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bishopRegularCauchyCompletionDecode_encode_bhist
  · constructor
    · exact bishopRegularCauchyCompletion_round_trip
    · constructor
      · intro x y heq
        exact bishopRegularCauchyCompletionToEventFlow_injective heq
      · rfl

end BEDC.Derived.BishopRegularCauchyCompletionUp
