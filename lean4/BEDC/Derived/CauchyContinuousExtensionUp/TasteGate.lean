import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyContinuousExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyContinuousExtensionUp : Type where
  | mk : (S W D F U L H C P N : BHist) → CauchyContinuousExtensionUp
  deriving DecidableEq

def cauchyContinuousExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyContinuousExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyContinuousExtensionEncodeBHist h

def cauchyContinuousExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyContinuousExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyContinuousExtensionDecodeBHist tail)

private theorem cauchyContinuousExtensionDecode_encode_bhist :
    ∀ h : BHist,
      cauchyContinuousExtensionDecodeBHist
        (cauchyContinuousExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyContinuousExtensionToEventFlow :
    CauchyContinuousExtensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyContinuousExtensionUp.mk S W D F U L H C P N =>
      [cauchyContinuousExtensionEncodeBHist S,
        cauchyContinuousExtensionEncodeBHist W,
        cauchyContinuousExtensionEncodeBHist D,
        cauchyContinuousExtensionEncodeBHist F,
        cauchyContinuousExtensionEncodeBHist U,
        cauchyContinuousExtensionEncodeBHist L,
        cauchyContinuousExtensionEncodeBHist H,
        cauchyContinuousExtensionEncodeBHist C,
        cauchyContinuousExtensionEncodeBHist P,
        cauchyContinuousExtensionEncodeBHist N]

def cauchyContinuousExtensionFromEventFlow :
    EventFlow → Option CauchyContinuousExtensionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | U :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
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
                                                (CauchyContinuousExtensionUp.mk
                                                  (cauchyContinuousExtensionDecodeBHist S)
                                                  (cauchyContinuousExtensionDecodeBHist W)
                                                  (cauchyContinuousExtensionDecodeBHist D)
                                                  (cauchyContinuousExtensionDecodeBHist F)
                                                  (cauchyContinuousExtensionDecodeBHist U)
                                                  (cauchyContinuousExtensionDecodeBHist L)
                                                  (cauchyContinuousExtensionDecodeBHist H)
                                                  (cauchyContinuousExtensionDecodeBHist C)
                                                  (cauchyContinuousExtensionDecodeBHist P)
                                                  (cauchyContinuousExtensionDecodeBHist N))
                                          | _ :: _ => none

def cauchyContinuousExtensionFields :
    CauchyContinuousExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyContinuousExtensionUp.mk S W D F U L H C P N => [S, W, D, F, U, L, H, C, P, N]

private theorem cauchyContinuousExtension_round_trip :
    ∀ x : CauchyContinuousExtensionUp,
      cauchyContinuousExtensionFromEventFlow
        (cauchyContinuousExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D F U L H C P N =>
      change
        some
          (CauchyContinuousExtensionUp.mk
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist S))
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist W))
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist D))
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist F))
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist U))
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist L))
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist H))
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist C))
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist P))
            (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist N))) =
          some (CauchyContinuousExtensionUp.mk S W D F U L H C P N)
      rw [cauchyContinuousExtensionDecode_encode_bhist S,
        cauchyContinuousExtensionDecode_encode_bhist W,
        cauchyContinuousExtensionDecode_encode_bhist D,
        cauchyContinuousExtensionDecode_encode_bhist F,
        cauchyContinuousExtensionDecode_encode_bhist U,
        cauchyContinuousExtensionDecode_encode_bhist L,
        cauchyContinuousExtensionDecode_encode_bhist H,
        cauchyContinuousExtensionDecode_encode_bhist C,
        cauchyContinuousExtensionDecode_encode_bhist P,
        cauchyContinuousExtensionDecode_encode_bhist N]

private theorem cauchyContinuousExtensionToEventFlow_injective
    {x y : CauchyContinuousExtensionUp} :
    cauchyContinuousExtensionToEventFlow x =
      cauchyContinuousExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyContinuousExtensionFromEventFlow
          (cauchyContinuousExtensionToEventFlow x) =
        cauchyContinuousExtensionFromEventFlow
          (cauchyContinuousExtensionToEventFlow y) :=
    congrArg cauchyContinuousExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyContinuousExtension_round_trip x).symm
      (Eq.trans hread (cauchyContinuousExtension_round_trip y)))

instance cauchyContinuousExtensionBHistCarrier :
    BHistCarrier CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyContinuousExtensionToEventFlow
  fromEventFlow := cauchyContinuousExtensionFromEventFlow

instance cauchyContinuousExtensionChapterTasteGate :
    ChapterTasteGate CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyContinuousExtensionFromEventFlow
        (cauchyContinuousExtensionToEventFlow x) = some x
    exact cauchyContinuousExtension_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyContinuousExtensionToEventFlow_injective heq)

instance cauchyContinuousExtensionFieldFaithful :
    FieldFaithful CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyContinuousExtensionFields
  field_faithful := by
    intro x y h
    cases x with
    | mk S₁ W₁ D₁ F₁ U₁ L₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk S₂ W₂ D₂ F₂ U₂ L₂ H₂ C₂ P₂ N₂ =>
            cases h
            rfl

instance cauchyContinuousExtensionNontrivial :
    Nontrivial CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyContinuousExtensionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyContinuousExtensionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyContinuousExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyContinuousExtensionChapterTasteGate

theorem CauchyContinuousExtensionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist h) = h) ∧
      (∀ x : CauchyContinuousExtensionUp,
        cauchyContinuousExtensionFromEventFlow
          (cauchyContinuousExtensionToEventFlow x) = some x) ∧
        (∀ x y : CauchyContinuousExtensionUp,
          cauchyContinuousExtensionToEventFlow x =
            cauchyContinuousExtensionToEventFlow y → x = y) ∧
          cauchyContinuousExtensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyContinuousExtensionDecode_encode_bhist
  · constructor
    · exact cauchyContinuousExtension_round_trip
    · constructor
      · intro x y heq
        exact cauchyContinuousExtensionToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyContinuousExtensionUp
