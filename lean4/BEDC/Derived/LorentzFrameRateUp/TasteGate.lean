import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LorentzFrameRateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LorentzFrameRateUp : Type where
  | mk :
      (multiConfig causalWitness maxRate symmetry transport route provenance name : BHist) →
        LorentzFrameRateUp
  deriving DecidableEq

def lorentzFrameRateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lorentzFrameRateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lorentzFrameRateEncodeBHist h

def lorentzFrameRateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lorentzFrameRateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lorentzFrameRateDecodeBHist tail)

private theorem lorentzFrameRateDecode_encode_bhist :
    ∀ h : BHist, lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def lorentzFrameRateToEventFlow : LorentzFrameRateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LorentzFrameRateUp.mk multiConfig causalWitness maxRate symmetry transport route provenance
      name =>
      [[BMark.b0],
        lorentzFrameRateEncodeBHist multiConfig,
        [BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist causalWitness,
        [BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist maxRate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist symmetry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        lorentzFrameRateEncodeBHist name]

def lorentzFrameRateFromEventFlow : EventFlow → Option LorentzFrameRateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | multiConfig :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | causalWitness :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | maxRate :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | symmetry :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (LorentzFrameRateUp.mk
                                                                          (lorentzFrameRateDecodeBHist
                                                                            multiConfig)
                                                                          (lorentzFrameRateDecodeBHist
                                                                            causalWitness)
                                                                          (lorentzFrameRateDecodeBHist
                                                                            maxRate)
                                                                          (lorentzFrameRateDecodeBHist
                                                                            symmetry)
                                                                          (lorentzFrameRateDecodeBHist
                                                                            transport)
                                                                          (lorentzFrameRateDecodeBHist
                                                                            route)
                                                                          (lorentzFrameRateDecodeBHist
                                                                            provenance)
                                                                          (lorentzFrameRateDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem lorentzFrameRate_round_trip :
    ∀ x : LorentzFrameRateUp,
      lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk multiConfig causalWitness maxRate symmetry transport route provenance name =>
      change
        some
          (LorentzFrameRateUp.mk
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist multiConfig))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist causalWitness))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist maxRate))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist symmetry))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist transport))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist route))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist provenance))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist name))) =
          some
            (LorentzFrameRateUp.mk multiConfig causalWitness maxRate symmetry transport route
              provenance name)
      rw [lorentzFrameRateDecode_encode_bhist multiConfig,
        lorentzFrameRateDecode_encode_bhist causalWitness,
        lorentzFrameRateDecode_encode_bhist maxRate,
        lorentzFrameRateDecode_encode_bhist symmetry,
        lorentzFrameRateDecode_encode_bhist transport,
        lorentzFrameRateDecode_encode_bhist route,
        lorentzFrameRateDecode_encode_bhist provenance,
        lorentzFrameRateDecode_encode_bhist name]

private theorem lorentzFrameRateToEventFlow_injective {x y : LorentzFrameRateUp} :
    lorentzFrameRateToEventFlow x = lorentzFrameRateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow x) =
        lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow y) :=
    congrArg lorentzFrameRateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lorentzFrameRate_round_trip x).symm
      (Eq.trans hread (lorentzFrameRate_round_trip y)))

instance lorentzFrameRateBHistCarrier : BHistCarrier LorentzFrameRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lorentzFrameRateToEventFlow
  fromEventFlow := lorentzFrameRateFromEventFlow

instance lorentzFrameRateChapterTasteGate : ChapterTasteGate LorentzFrameRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow x) = some x
    exact lorentzFrameRate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lorentzFrameRateToEventFlow_injective heq)

instance lorentzFrameRateFieldFaithful : FieldFaithful LorentzFrameRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LorentzFrameRateUp.mk multiConfig causalWitness maxRate symmetry transport route provenance
        name =>
        [multiConfig, causalWitness, maxRate, symmetry, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk multiConfig1 causalWitness1 maxRate1 symmetry1 transport1 route1 provenance1 name1 =>
        cases y with
        | mk multiConfig2 causalWitness2 maxRate2 symmetry2 transport2 route2 provenance2 name2 =>
            cases h
            rfl

instance lorentzFrameRateNontrivial : Nontrivial LorentzFrameRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LorentzFrameRateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      LorentzFrameRateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LorentzFrameRateTasteGate_single_carrier_alignment :
    (∀ h : BHist, lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist h) = h) ∧
      (∀ x : LorentzFrameRateUp,
        lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow x) = some x) ∧
        (∀ x y : LorentzFrameRateUp,
          lorentzFrameRateToEventFlow x = lorentzFrameRateToEventFlow y → x = y) ∧
          lorentzFrameRateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact lorentzFrameRateDecode_encode_bhist
  · constructor
    · exact lorentzFrameRate_round_trip
    · constructor
      · intro x y heq
        exact lorentzFrameRateToEventFlow_injective heq
      · rfl

theorem LorentzFrameRateUpstreamRowCoherence
    {multiConfig causalWitness maxRate symmetry transport route provenance name upstream :
      BHist} :
    Cont multiConfig causalWitness upstream →
      Cont upstream maxRate route →
        UnaryHistory multiConfig →
          UnaryHistory causalWitness →
            UnaryHistory maxRate →
              UnaryHistory upstream ∧ UnaryHistory route ∧
                Cont multiConfig causalWitness upstream ∧ Cont upstream maxRate route ∧
                  (fun x : LorentzFrameRateUp =>
                    match x with
                    | LorentzFrameRateUp.mk m x r _ _ _ _ _ =>
                        m = multiConfig ∧ x = causalWitness ∧ r = maxRate)
                    (LorentzFrameRateUp.mk multiConfig causalWitness maxRate symmetry transport
                      route provenance name) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro multiCausalUpstream upstreamMaxRoute multiUnary causalUnary maxUnary
  have upstreamUnary : UnaryHistory upstream :=
    unary_cont_closed multiUnary causalUnary multiCausalUpstream
  have routeUnary : UnaryHistory route :=
    unary_cont_closed upstreamUnary maxUnary upstreamMaxRoute
  exact
    ⟨upstreamUnary, routeUnary, multiCausalUpstream, upstreamMaxRoute, rfl, rfl, rfl⟩

theorem LorentzFrameRateRootRouteTotality
    {multiConfig causalWitness maxRate symmetry transport route provenance name upstream
      classifierReplay publicRoute : BHist} :
    Cont multiConfig causalWitness upstream →
      Cont upstream maxRate route →
        Cont route symmetry classifierReplay →
          Cont classifierReplay transport publicRoute →
            UnaryHistory multiConfig →
              UnaryHistory causalWitness →
                UnaryHistory maxRate →
                  UnaryHistory symmetry →
                    UnaryHistory transport →
                      UnaryHistory upstream ∧ UnaryHistory route ∧
                        UnaryHistory classifierReplay ∧ UnaryHistory publicRoute ∧
                          Cont multiConfig causalWitness upstream ∧
                            Cont upstream maxRate route ∧
                              Cont route symmetry classifierReplay ∧
                                Cont classifierReplay transport publicRoute ∧
                                  (fun x : LorentzFrameRateUp =>
                                    match x with
                                    | LorentzFrameRateUp.mk m x r s h _ _ _ =>
                                        m = multiConfig ∧ x = causalWitness ∧
                                          r = maxRate ∧ s = symmetry ∧ h = transport)
                                  (LorentzFrameRateUp.mk multiConfig causalWitness maxRate
                                    symmetry transport route provenance name) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro multiCausalUpstream upstreamMaxRoute routeSymmetryClassifier
    classifierTransportPublic multiUnary causalUnary maxUnary symmetryUnary transportUnary
  have upstreamUnary : UnaryHistory upstream :=
    unary_cont_closed multiUnary causalUnary multiCausalUpstream
  have routeUnary : UnaryHistory route :=
    unary_cont_closed upstreamUnary maxUnary upstreamMaxRoute
  have classifierReplayUnary : UnaryHistory classifierReplay :=
    unary_cont_closed routeUnary symmetryUnary routeSymmetryClassifier
  have publicRouteUnary : UnaryHistory publicRoute :=
    unary_cont_closed classifierReplayUnary transportUnary classifierTransportPublic
  exact
    ⟨upstreamUnary, routeUnary, classifierReplayUnary, publicRouteUnary,
      multiCausalUpstream, upstreamMaxRoute, routeSymmetryClassifier,
      classifierTransportPublic, rfl, rfl, rfl, rfl, rfl⟩

def taste_gate : ChapterTasteGate LorentzFrameRateUp :=
  lorentzFrameRateChapterTasteGate

end BEDC.Derived.LorentzFrameRateUp
