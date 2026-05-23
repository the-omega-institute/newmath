import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorDiagonalRealUncountabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorDiagonalRealUncountabilityUp : Type where
  | mk (E W B Q R S H K P N : BHist) : CantorDiagonalRealUncountabilityUp
  deriving DecidableEq

def cantorDiagonalRealUncountabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorDiagonalRealUncountabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorDiagonalRealUncountabilityEncodeBHist h

def cantorDiagonalRealUncountabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorDiagonalRealUncountabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorDiagonalRealUncountabilityDecodeBHist tail)

private theorem cantorDiagonalRealUncountabilityDecode_encode :
    ∀ h : BHist,
      cantorDiagonalRealUncountabilityDecodeBHist
          (cantorDiagonalRealUncountabilityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorDiagonalRealUncountabilityFields :
    CantorDiagonalRealUncountabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorDiagonalRealUncountabilityUp.mk E W B Q R S H K P N =>
      [E, W, B, Q, R, S, H, K, P, N]

def cantorDiagonalRealUncountabilityToEventFlow :
    CantorDiagonalRealUncountabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cantorDiagonalRealUncountabilityFields x).map
        cantorDiagonalRealUncountabilityEncodeBHist

def cantorDiagonalRealUncountabilityFromEventFlow :
    EventFlow → Option CantorDiagonalRealUncountabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | K :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CantorDiagonalRealUncountabilityUp.mk
                                                  (cantorDiagonalRealUncountabilityDecodeBHist E)
                                                  (cantorDiagonalRealUncountabilityDecodeBHist W)
                                                  (cantorDiagonalRealUncountabilityDecodeBHist B)
                                                  (cantorDiagonalRealUncountabilityDecodeBHist Q)
                                                  (cantorDiagonalRealUncountabilityDecodeBHist R)
                                                  (cantorDiagonalRealUncountabilityDecodeBHist S)
                                                  (cantorDiagonalRealUncountabilityDecodeBHist H)
                                                  (cantorDiagonalRealUncountabilityDecodeBHist K)
                                                  (cantorDiagonalRealUncountabilityDecodeBHist P)
                                                  (cantorDiagonalRealUncountabilityDecodeBHist N))
                                          | _ :: _ => none

private theorem cantorDiagonalRealUncountability_round_trip :
    ∀ x : CantorDiagonalRealUncountabilityUp,
      cantorDiagonalRealUncountabilityFromEventFlow
          (cantorDiagonalRealUncountabilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E W B Q R S H K P N =>
      change
        some
          (CantorDiagonalRealUncountabilityUp.mk
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist E))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist W))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist B))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist Q))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist R))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist S))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist H))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist K))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist P))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist N))) =
          some (CantorDiagonalRealUncountabilityUp.mk E W B Q R S H K P N)
      rw [cantorDiagonalRealUncountabilityDecode_encode E,
        cantorDiagonalRealUncountabilityDecode_encode W,
        cantorDiagonalRealUncountabilityDecode_encode B,
        cantorDiagonalRealUncountabilityDecode_encode Q,
        cantorDiagonalRealUncountabilityDecode_encode R,
        cantorDiagonalRealUncountabilityDecode_encode S,
        cantorDiagonalRealUncountabilityDecode_encode H,
        cantorDiagonalRealUncountabilityDecode_encode K,
        cantorDiagonalRealUncountabilityDecode_encode P,
        cantorDiagonalRealUncountabilityDecode_encode N]

private theorem cantorDiagonalRealUncountabilityToEventFlow_injective
    {x y : CantorDiagonalRealUncountabilityUp} :
    cantorDiagonalRealUncountabilityToEventFlow x =
        cantorDiagonalRealUncountabilityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          cantorDiagonalRealUncountabilityFromEventFlow
            (cantorDiagonalRealUncountabilityToEventFlow x) :=
        (cantorDiagonalRealUncountability_round_trip x).symm
      _ =
          cantorDiagonalRealUncountabilityFromEventFlow
            (cantorDiagonalRealUncountabilityToEventFlow y) :=
        congrArg cantorDiagonalRealUncountabilityFromEventFlow hxy
      _ = some y := cantorDiagonalRealUncountability_round_trip y
  exact Option.some.inj optionEq

private theorem cantorDiagonalRealUncountability_field_faithful :
    ∀ x y : CantorDiagonalRealUncountabilityUp,
      cantorDiagonalRealUncountabilityFields x =
          cantorDiagonalRealUncountabilityFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ W₁ B₁ Q₁ R₁ S₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk E₂ W₂ B₂ Q₂ R₂ S₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance cantorDiagonalRealUncountabilityBHistCarrier :
    BHistCarrier CantorDiagonalRealUncountabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorDiagonalRealUncountabilityToEventFlow
  fromEventFlow := cantorDiagonalRealUncountabilityFromEventFlow

instance cantorDiagonalRealUncountabilityChapterTasteGate :
    ChapterTasteGate CantorDiagonalRealUncountabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cantorDiagonalRealUncountabilityFromEventFlow
          (cantorDiagonalRealUncountabilityToEventFlow x) =
        some x
    exact cantorDiagonalRealUncountability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cantorDiagonalRealUncountabilityToEventFlow_injective heq)

instance cantorDiagonalRealUncountabilityFieldFaithful :
    FieldFaithful CantorDiagonalRealUncountabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cantorDiagonalRealUncountabilityFields
  field_faithful := cantorDiagonalRealUncountability_field_faithful

def taste_gate : ChapterTasteGate CantorDiagonalRealUncountabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorDiagonalRealUncountabilityChapterTasteGate

theorem CantorDiagonalRealUncountabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cantorDiagonalRealUncountabilityDecodeBHist
          (cantorDiagonalRealUncountabilityEncodeBHist h) =
        h) ∧
      (∀ x : CantorDiagonalRealUncountabilityUp,
        cantorDiagonalRealUncountabilityFromEventFlow
            (cantorDiagonalRealUncountabilityToEventFlow x) =
          some x) ∧
        (∀ x y : CantorDiagonalRealUncountabilityUp,
          cantorDiagonalRealUncountabilityToEventFlow x =
              cantorDiagonalRealUncountabilityToEventFlow y →
            x = y) ∧
          cantorDiagonalRealUncountabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact cantorDiagonalRealUncountabilityDecode_encode
  · constructor
    · exact cantorDiagonalRealUncountability_round_trip
    · constructor
      · intro x y heq
        exact cantorDiagonalRealUncountabilityToEventFlow_injective heq
      · rfl

end BEDC.Derived.CantorDiagonalRealUncountabilityUp
