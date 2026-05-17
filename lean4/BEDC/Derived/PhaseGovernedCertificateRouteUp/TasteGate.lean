import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhaseGovernedCertificateRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhaseGovernedCertificateRouteUp : Type where
  | mk : (A S F E D U H C P N : BHist) → PhaseGovernedCertificateRouteUp
  deriving DecidableEq

def phaseGovernedCertificateRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: phaseGovernedCertificateRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: phaseGovernedCertificateRouteEncodeBHist h

def phaseGovernedCertificateRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (phaseGovernedCertificateRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (phaseGovernedCertificateRouteDecodeBHist tail)

private theorem phaseGovernedCertificateRoute_decode_encode_bhist :
    ∀ h : BHist,
      phaseGovernedCertificateRouteDecodeBHist
        (phaseGovernedCertificateRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def phaseGovernedCertificateRouteToEventFlow :
    PhaseGovernedCertificateRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhaseGovernedCertificateRouteUp.mk A S F E D U H C P N =>
      [[BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist A,
        [BMark.b1, BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        phaseGovernedCertificateRouteEncodeBHist N]

def phaseGovernedCertificateRouteFromEventFlow :
    EventFlow → Option PhaseGovernedCertificateRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
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
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | D :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | U :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (PhaseGovernedCertificateRouteUp.mk
                                                                                          (phaseGovernedCertificateRouteDecodeBHist A)
                                                                                          (phaseGovernedCertificateRouteDecodeBHist S)
                                                                                          (phaseGovernedCertificateRouteDecodeBHist F)
                                                                                          (phaseGovernedCertificateRouteDecodeBHist E)
                                                                                          (phaseGovernedCertificateRouteDecodeBHist D)
                                                                                          (phaseGovernedCertificateRouteDecodeBHist U)
                                                                                          (phaseGovernedCertificateRouteDecodeBHist H)
                                                                                          (phaseGovernedCertificateRouteDecodeBHist C)
                                                                                          (phaseGovernedCertificateRouteDecodeBHist P)
                                                                                          (phaseGovernedCertificateRouteDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem phaseGovernedCertificateRoute_round_trip :
    ∀ x : PhaseGovernedCertificateRouteUp,
      phaseGovernedCertificateRouteFromEventFlow
        (phaseGovernedCertificateRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A S F E D U H C P N =>
      change
        some
          (PhaseGovernedCertificateRouteUp.mk
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist A))
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist S))
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist F))
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist E))
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist D))
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist U))
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist H))
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist C))
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist P))
            (phaseGovernedCertificateRouteDecodeBHist
              (phaseGovernedCertificateRouteEncodeBHist N))) =
          some (PhaseGovernedCertificateRouteUp.mk A S F E D U H C P N)
      rw [phaseGovernedCertificateRoute_decode_encode_bhist A,
        phaseGovernedCertificateRoute_decode_encode_bhist S,
        phaseGovernedCertificateRoute_decode_encode_bhist F,
        phaseGovernedCertificateRoute_decode_encode_bhist E,
        phaseGovernedCertificateRoute_decode_encode_bhist D,
        phaseGovernedCertificateRoute_decode_encode_bhist U,
        phaseGovernedCertificateRoute_decode_encode_bhist H,
        phaseGovernedCertificateRoute_decode_encode_bhist C,
        phaseGovernedCertificateRoute_decode_encode_bhist P,
        phaseGovernedCertificateRoute_decode_encode_bhist N]

private theorem phaseGovernedCertificateRouteToEventFlow_injective
    {x y : PhaseGovernedCertificateRouteUp} :
    phaseGovernedCertificateRouteToEventFlow x =
      phaseGovernedCertificateRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      phaseGovernedCertificateRouteFromEventFlow
          (phaseGovernedCertificateRouteToEventFlow x) =
        phaseGovernedCertificateRouteFromEventFlow
          (phaseGovernedCertificateRouteToEventFlow y) :=
    congrArg phaseGovernedCertificateRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (phaseGovernedCertificateRoute_round_trip x).symm
      (Eq.trans hread (phaseGovernedCertificateRoute_round_trip y)))

def phaseGovernedCertificateRouteFields :
    PhaseGovernedCertificateRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhaseGovernedCertificateRouteUp.mk A S F E D U H C P N =>
      [A, S, F, E, D, U, H, C, P, N]

private theorem phaseGovernedCertificateRoute_field_faithful :
    ∀ x y : PhaseGovernedCertificateRouteUp,
      phaseGovernedCertificateRouteFields x =
        phaseGovernedCertificateRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk A₁ S₁ F₁ E₁ D₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ S₂ F₂ E₂ D₂ U₂ H₂ C₂ P₂ N₂ =>
          injection h with hA t1
          injection t1 with hS t2
          injection t2 with hF t3
          injection t3 with hE t4
          injection t4 with hD t5
          injection t5 with hU t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          cases hA
          cases hS
          cases hF
          cases hE
          cases hD
          cases hU
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance phaseGovernedCertificateRouteBHistCarrier :
    BHistCarrier PhaseGovernedCertificateRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := phaseGovernedCertificateRouteToEventFlow
  fromEventFlow := phaseGovernedCertificateRouteFromEventFlow

instance phaseGovernedCertificateRouteChapterTasteGate :
    ChapterTasteGate PhaseGovernedCertificateRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      phaseGovernedCertificateRouteFromEventFlow
          (phaseGovernedCertificateRouteToEventFlow x) =
        some x
    exact phaseGovernedCertificateRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (phaseGovernedCertificateRouteToEventFlow_injective heq)

instance phaseGovernedCertificateRouteFieldFaithful :
    FieldFaithful PhaseGovernedCertificateRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := phaseGovernedCertificateRouteFields
  field_faithful := phaseGovernedCertificateRoute_field_faithful

instance phaseGovernedCertificateRouteNontrivial :
    Nontrivial PhaseGovernedCertificateRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhaseGovernedCertificateRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhaseGovernedCertificateRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PhaseGovernedCertificateRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      phaseGovernedCertificateRouteDecodeBHist
        (phaseGovernedCertificateRouteEncodeBHist h) = h) ∧
      (∀ x : PhaseGovernedCertificateRouteUp,
        phaseGovernedCertificateRouteFromEventFlow
          (phaseGovernedCertificateRouteToEventFlow x) = some x) ∧
        (∀ x y : PhaseGovernedCertificateRouteUp,
          phaseGovernedCertificateRouteToEventFlow x =
            phaseGovernedCertificateRouteToEventFlow y → x = y) ∧
          phaseGovernedCertificateRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact phaseGovernedCertificateRoute_decode_encode_bhist
  · constructor
    · exact phaseGovernedCertificateRoute_round_trip
    · constructor
      · intro x y heq
        exact phaseGovernedCertificateRouteToEventFlow_injective heq
      · rfl

end BEDC.Derived.PhaseGovernedCertificateRouteUp
