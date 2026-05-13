import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BetaSubstitutionPreservationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BetaSubstitutionPreservationUp : Type where
  | mk :
      (body argument redex codomain substitutedBody substitutedCodomain ledger transport routes
        provenance name : BHist) →
      BetaSubstitutionPreservationUp
  deriving DecidableEq

def betaSubstitutionPreservationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: betaSubstitutionPreservationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: betaSubstitutionPreservationEncodeBHist h

def betaSubstitutionPreservationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (betaSubstitutionPreservationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (betaSubstitutionPreservationDecodeBHist tail)

private theorem betaSubstitutionPreservationDecode_encode_bhist :
    ∀ h : BHist,
      betaSubstitutionPreservationDecodeBHist
          (betaSubstitutionPreservationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem betaSubstitutionPreservation_mk_congr
    {body body' argument argument' redex redex' codomain codomain' substitutedBody
      substitutedBody' substitutedCodomain substitutedCodomain' ledger ledger' transport
      transport' routes routes' provenance provenance' name name' : BHist}
    (hBody : body' = body)
    (hArgument : argument' = argument)
    (hRedex : redex' = redex)
    (hCodomain : codomain' = codomain)
    (hSubstitutedBody : substitutedBody' = substitutedBody)
    (hSubstitutedCodomain : substitutedCodomain' = substitutedCodomain)
    (hLedger : ledger' = ledger)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    BetaSubstitutionPreservationUp.mk body' argument' redex' codomain' substitutedBody'
        substitutedCodomain' ledger' transport' routes' provenance' name' =
      BetaSubstitutionPreservationUp.mk body argument redex codomain substitutedBody
        substitutedCodomain ledger transport routes provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hBody
  cases hArgument
  cases hRedex
  cases hCodomain
  cases hSubstitutedBody
  cases hSubstitutedCodomain
  cases hLedger
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hName
  rfl

def betaSubstitutionPreservationToEventFlow :
    BetaSubstitutionPreservationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BetaSubstitutionPreservationUp.mk body argument redex codomain substitutedBody
      substitutedCodomain ledger transport routes provenance name =>
      [[BMark.b0],
        betaSubstitutionPreservationEncodeBHist body,
        [BMark.b1, BMark.b0],
        betaSubstitutionPreservationEncodeBHist argument,
        [BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationEncodeBHist redex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationEncodeBHist codomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationEncodeBHist substitutedBody,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationEncodeBHist substitutedCodomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        betaSubstitutionPreservationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        betaSubstitutionPreservationEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationEncodeBHist name]

def betaSubstitutionPreservationFromEventFlow :
    EventFlow → Option BetaSubstitutionPreservationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | body :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | argument :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | redex :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | codomain :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | substitutedBody :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | substitutedCodomain :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | ledger :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | routes ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | name ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              some
                                                                                                (BetaSubstitutionPreservationUp.mk
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    body)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    argument)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    redex)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    codomain)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    substitutedBody)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    substitutedCodomain)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    ledger)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    transport)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    routes)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    provenance)
                                                                                                  (betaSubstitutionPreservationDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem betaSubstitutionPreservation_round_trip :
    ∀ x : BetaSubstitutionPreservationUp,
      betaSubstitutionPreservationFromEventFlow
          (betaSubstitutionPreservationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk body argument redex codomain substitutedBody substitutedCodomain ledger transport
      routes provenance name =>
      change
        some
          (BetaSubstitutionPreservationUp.mk
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist body))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist argument))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist redex))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist codomain))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist substitutedBody))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist substitutedCodomain))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist ledger))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist transport))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist routes))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist provenance))
            (betaSubstitutionPreservationDecodeBHist
              (betaSubstitutionPreservationEncodeBHist name))) =
          some
            (BetaSubstitutionPreservationUp.mk body argument redex codomain
              substitutedBody substitutedCodomain ledger transport routes provenance name)
      exact
        congrArg some
          (betaSubstitutionPreservation_mk_congr
            (betaSubstitutionPreservationDecode_encode_bhist body)
            (betaSubstitutionPreservationDecode_encode_bhist argument)
            (betaSubstitutionPreservationDecode_encode_bhist redex)
            (betaSubstitutionPreservationDecode_encode_bhist codomain)
            (betaSubstitutionPreservationDecode_encode_bhist substitutedBody)
            (betaSubstitutionPreservationDecode_encode_bhist substitutedCodomain)
            (betaSubstitutionPreservationDecode_encode_bhist ledger)
            (betaSubstitutionPreservationDecode_encode_bhist transport)
            (betaSubstitutionPreservationDecode_encode_bhist routes)
            (betaSubstitutionPreservationDecode_encode_bhist provenance)
            (betaSubstitutionPreservationDecode_encode_bhist name))

private theorem betaSubstitutionPreservationToEventFlow_injective
    {x y : BetaSubstitutionPreservationUp} :
    betaSubstitutionPreservationToEventFlow x =
        betaSubstitutionPreservationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      betaSubstitutionPreservationFromEventFlow
          (betaSubstitutionPreservationToEventFlow x) =
        betaSubstitutionPreservationFromEventFlow
          (betaSubstitutionPreservationToEventFlow y) :=
    congrArg betaSubstitutionPreservationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (betaSubstitutionPreservation_round_trip x).symm
      (Eq.trans hread (betaSubstitutionPreservation_round_trip y)))

instance betaSubstitutionPreservationBHistCarrier :
    BHistCarrier BetaSubstitutionPreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := betaSubstitutionPreservationToEventFlow
  fromEventFlow := betaSubstitutionPreservationFromEventFlow

instance betaSubstitutionPreservationChapterTasteGate :
    ChapterTasteGate BetaSubstitutionPreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      betaSubstitutionPreservationFromEventFlow
          (betaSubstitutionPreservationToEventFlow x) =
        some x
    exact betaSubstitutionPreservation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (betaSubstitutionPreservationToEventFlow_injective heq)

theorem BetaSubstitutionPreservationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      betaSubstitutionPreservationDecodeBHist
          (betaSubstitutionPreservationEncodeBHist h) =
        h) ∧
      (∀ x : BetaSubstitutionPreservationUp,
        betaSubstitutionPreservationFromEventFlow
            (betaSubstitutionPreservationToEventFlow x) =
          some x) ∧
        (∀ x y : BetaSubstitutionPreservationUp,
          betaSubstitutionPreservationToEventFlow x =
              betaSubstitutionPreservationToEventFlow y →
            x = y) ∧
          betaSubstitutionPreservationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    And.intro betaSubstitutionPreservationDecode_encode_bhist
      (And.intro betaSubstitutionPreservation_round_trip
        (And.intro
          (fun x y heq => betaSubstitutionPreservationToEventFlow_injective heq)
          rfl))

end BEDC.Derived.BetaSubstitutionPreservationUp
