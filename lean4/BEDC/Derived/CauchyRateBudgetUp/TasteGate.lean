import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRateBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRateBudgetUp : Type where
  | mk : (R W Q D E H C P N : BHist) → CauchyRateBudgetUp
  deriving DecidableEq

def cauchyRateBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRateBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRateBudgetEncodeBHist h

def cauchyRateBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRateBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRateBudgetDecodeBHist tail)

private theorem cauchyRateBudgetDecodeEncodeBHist :
    ∀ h : BHist, cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyRateBudgetFields : CauchyRateBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRateBudgetUp.mk R W Q D E H C P N => [R, W, Q, D, E, H, C, P, N]

def cauchyRateBudgetToEventFlow : CauchyRateBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRateBudgetFields x).map cauchyRateBudgetEncodeBHist

def cauchyRateBudgetFromEventFlow : EventFlow → Option CauchyRateBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
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
                                            (CauchyRateBudgetUp.mk
                                              (cauchyRateBudgetDecodeBHist R)
                                              (cauchyRateBudgetDecodeBHist W)
                                              (cauchyRateBudgetDecodeBHist Q)
                                              (cauchyRateBudgetDecodeBHist D)
                                              (cauchyRateBudgetDecodeBHist E)
                                              (cauchyRateBudgetDecodeBHist H)
                                              (cauchyRateBudgetDecodeBHist C)
                                              (cauchyRateBudgetDecodeBHist P)
                                              (cauchyRateBudgetDecodeBHist N))
                                      | _ :: _ => none

private theorem cauchyRateBudget_round_trip :
    ∀ x : CauchyRateBudgetUp,
      cauchyRateBudgetFromEventFlow (cauchyRateBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W Q D E H C P N =>
      change
        some
          (CauchyRateBudgetUp.mk
            (cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist R))
            (cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist W))
            (cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist Q))
            (cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist D))
            (cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist E))
            (cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist H))
            (cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist C))
            (cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist P))
            (cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist N))) =
          some (CauchyRateBudgetUp.mk R W Q D E H C P N)
      rw [cauchyRateBudgetDecodeEncodeBHist R, cauchyRateBudgetDecodeEncodeBHist W,
        cauchyRateBudgetDecodeEncodeBHist Q, cauchyRateBudgetDecodeEncodeBHist D,
        cauchyRateBudgetDecodeEncodeBHist E, cauchyRateBudgetDecodeEncodeBHist H,
        cauchyRateBudgetDecodeEncodeBHist C, cauchyRateBudgetDecodeEncodeBHist P,
        cauchyRateBudgetDecodeEncodeBHist N]

private theorem cauchyRateBudgetToEventFlow_injective {x y : CauchyRateBudgetUp} :
    cauchyRateBudgetToEventFlow x = cauchyRateBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRateBudgetFromEventFlow (cauchyRateBudgetToEventFlow x) =
        cauchyRateBudgetFromEventFlow (cauchyRateBudgetToEventFlow y) :=
    congrArg cauchyRateBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRateBudget_round_trip x).symm
      (Eq.trans hread (cauchyRateBudget_round_trip y)))

private theorem cauchyRateBudget_fields_faithful :
    ∀ x y : CauchyRateBudgetUp,
      cauchyRateBudgetFields x = cauchyRateBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ W₁ Q₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ W₂ Q₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hR tail0
          injection tail0 with hW tail1
          injection tail1 with hQ tail2
          injection tail2 with hD tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hR
          subst hW
          subst hQ
          subst hD
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyRateBudgetBHistCarrier : BHistCarrier CauchyRateBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRateBudgetToEventFlow
  fromEventFlow := cauchyRateBudgetFromEventFlow

instance cauchyRateBudgetChapterTasteGate : ChapterTasteGate CauchyRateBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRateBudgetFromEventFlow (cauchyRateBudgetToEventFlow x) = some x
    exact cauchyRateBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRateBudgetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyRateBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRateBudgetFromEventFlow (cauchyRateBudgetToEventFlow x) = some x
    exact cauchyRateBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRateBudgetToEventFlow_injective heq)

instance cauchyRateBudgetFieldFaithful : FieldFaithful CauchyRateBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRateBudgetFields
  field_faithful := cauchyRateBudget_fields_faithful

instance cauchyRateBudgetNontrivial : Nontrivial CauchyRateBudgetUp where
  witness_pair :=
    ⟨CauchyRateBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRateBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem CauchyRateBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRateBudgetDecodeBHist (cauchyRateBudgetEncodeBHist h) = h) ∧
      (∀ x : CauchyRateBudgetUp,
        cauchyRateBudgetFromEventFlow (cauchyRateBudgetToEventFlow x) = some x) ∧
        (∀ x y : CauchyRateBudgetUp,
          cauchyRateBudgetToEventFlow x = cauchyRateBudgetToEventFlow y → x = y) ∧
          cauchyRateBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyRateBudgetDecodeEncodeBHist
  · constructor
    · exact cauchyRateBudget_round_trip
    · constructor
      · intro x y heq
        exact cauchyRateBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyRateBudgetUp
