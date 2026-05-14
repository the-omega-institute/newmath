import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFiniteObservationRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFiniteObservationRouteUp : Type where
  | mk : (Q W D R B S H C P N : BHist) → RegularCauchyFiniteObservationRouteUp
  deriving DecidableEq

def regularCauchyFiniteObservationRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFiniteObservationRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFiniteObservationRouteEncodeBHist h

def regularCauchyFiniteObservationRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFiniteObservationRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFiniteObservationRouteDecodeBHist tail)

private theorem regularCauchyFiniteObservationRouteDecodeEncodeBHist :
    ∀ h : BHist,
      regularCauchyFiniteObservationRouteDecodeBHist
        (regularCauchyFiniteObservationRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyFiniteObservationRouteFields :
    RegularCauchyFiniteObservationRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFiniteObservationRouteUp.mk Q W D R B S H C P N =>
      [Q, W, D, R, B, S, H, C, P, N]

def regularCauchyFiniteObservationRouteToEventFlow :
    RegularCauchyFiniteObservationRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyFiniteObservationRouteFields x).map
        regularCauchyFiniteObservationRouteEncodeBHist

def regularCauchyFiniteObservationRouteFromEventFlow :
    EventFlow → Option RegularCauchyFiniteObservationRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Q :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
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
                                                (RegularCauchyFiniteObservationRouteUp.mk
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    Q)
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    W)
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    D)
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    R)
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    B)
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    S)
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    H)
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    C)
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    P)
                                                  (regularCauchyFiniteObservationRouteDecodeBHist
                                                    N))
                                          | _ :: _ => none

private theorem regularCauchyFiniteObservationRoute_round_trip :
    ∀ x : RegularCauchyFiniteObservationRouteUp,
      regularCauchyFiniteObservationRouteFromEventFlow
        (regularCauchyFiniteObservationRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q W D R B S H C P N =>
      change
        some
          (RegularCauchyFiniteObservationRouteUp.mk
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist Q))
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist W))
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist D))
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist R))
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist B))
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist S))
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist H))
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist C))
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist P))
            (regularCauchyFiniteObservationRouteDecodeBHist
              (regularCauchyFiniteObservationRouteEncodeBHist N))) =
          some (RegularCauchyFiniteObservationRouteUp.mk Q W D R B S H C P N)
      rw [regularCauchyFiniteObservationRouteDecodeEncodeBHist Q,
        regularCauchyFiniteObservationRouteDecodeEncodeBHist W,
        regularCauchyFiniteObservationRouteDecodeEncodeBHist D,
        regularCauchyFiniteObservationRouteDecodeEncodeBHist R,
        regularCauchyFiniteObservationRouteDecodeEncodeBHist B,
        regularCauchyFiniteObservationRouteDecodeEncodeBHist S,
        regularCauchyFiniteObservationRouteDecodeEncodeBHist H,
        regularCauchyFiniteObservationRouteDecodeEncodeBHist C,
        regularCauchyFiniteObservationRouteDecodeEncodeBHist P,
        regularCauchyFiniteObservationRouteDecodeEncodeBHist N]

private theorem regularCauchyFiniteObservationRouteToEventFlow_injective
    {x y : RegularCauchyFiniteObservationRouteUp} :
    regularCauchyFiniteObservationRouteToEventFlow x =
      regularCauchyFiniteObservationRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFiniteObservationRouteFromEventFlow
          (regularCauchyFiniteObservationRouteToEventFlow x) =
        regularCauchyFiniteObservationRouteFromEventFlow
          (regularCauchyFiniteObservationRouteToEventFlow y) :=
    congrArg regularCauchyFiniteObservationRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyFiniteObservationRoute_round_trip x).symm
      (Eq.trans hread (regularCauchyFiniteObservationRoute_round_trip y)))

private theorem regularCauchyFiniteObservationRoute_fields_faithful :
    ∀ x y : RegularCauchyFiniteObservationRouteUp,
      regularCauchyFiniteObservationRouteFields x =
        regularCauchyFiniteObservationRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q₁ W₁ D₁ R₁ B₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ W₂ D₂ R₂ B₂ S₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hQ tail0
          injection tail0 with hW tail1
          injection tail1 with hD tail2
          injection tail2 with hR tail3
          injection tail3 with hB tail4
          injection tail4 with hS tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hQ
          subst hW
          subst hD
          subst hR
          subst hB
          subst hS
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyFiniteObservationRouteBHistCarrier :
    BHistCarrier RegularCauchyFiniteObservationRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFiniteObservationRouteToEventFlow
  fromEventFlow := regularCauchyFiniteObservationRouteFromEventFlow

instance regularCauchyFiniteObservationRouteChapterTasteGate :
    ChapterTasteGate RegularCauchyFiniteObservationRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyFiniteObservationRouteFromEventFlow
      (regularCauchyFiniteObservationRouteToEventFlow x) = some x
    exact regularCauchyFiniteObservationRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyFiniteObservationRouteToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyFiniteObservationRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyFiniteObservationRouteFromEventFlow
      (regularCauchyFiniteObservationRouteToEventFlow x) = some x
    exact regularCauchyFiniteObservationRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyFiniteObservationRouteToEventFlow_injective heq)

instance regularCauchyFiniteObservationRouteFieldFaithful :
    FieldFaithful RegularCauchyFiniteObservationRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyFiniteObservationRouteFields
  field_faithful := regularCauchyFiniteObservationRoute_fields_faithful

instance regularCauchyFiniteObservationRouteNontrivial :
    Nontrivial RegularCauchyFiniteObservationRouteUp where
  witness_pair :=
    ⟨RegularCauchyFiniteObservationRouteUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyFiniteObservationRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem RegularCauchyFiniteObservationRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyFiniteObservationRouteDecodeBHist
        (regularCauchyFiniteObservationRouteEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyFiniteObservationRouteUp,
        regularCauchyFiniteObservationRouteFromEventFlow
          (regularCauchyFiniteObservationRouteToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyFiniteObservationRouteUp,
          regularCauchyFiniteObservationRouteToEventFlow x =
            regularCauchyFiniteObservationRouteToEventFlow y → x = y) ∧
          regularCauchyFiniteObservationRouteEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyFiniteObservationRouteDecodeEncodeBHist
  · constructor
    · exact regularCauchyFiniteObservationRoute_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyFiniteObservationRouteToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyFiniteObservationRouteUp
