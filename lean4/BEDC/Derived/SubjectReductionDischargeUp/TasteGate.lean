import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionDischargeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectReductionDischargeUp : Type where
  | mk :
      (beta appArg lamDomain piDomain substitution compiler obstruction transport routes
        provenance name : BHist) →
      SubjectReductionDischargeUp
  deriving DecidableEq

def subjectReductionDischargeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionDischargeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionDischargeEncodeBHist h

def subjectReductionDischargeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionDischargeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionDischargeDecodeBHist tail)

private theorem subjectReductionDischargeDecode_encode_bhist :
    ∀ h : BHist,
      subjectReductionDischargeDecodeBHist (subjectReductionDischargeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem subjectReductionDischarge_mk_congr
    {beta beta' appArg appArg' lamDomain lamDomain' piDomain piDomain' substitution
      substitution' compiler compiler' obstruction obstruction' transport transport' routes
      routes' provenance provenance' name name' : BHist}
    (hBeta : beta' = beta)
    (hAppArg : appArg' = appArg)
    (hLamDomain : lamDomain' = lamDomain)
    (hPiDomain : piDomain' = piDomain)
    (hSubstitution : substitution' = substitution)
    (hCompiler : compiler' = compiler)
    (hObstruction : obstruction' = obstruction)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    SubjectReductionDischargeUp.mk beta' appArg' lamDomain' piDomain' substitution' compiler'
        obstruction' transport' routes' provenance' name' =
      SubjectReductionDischargeUp.mk beta appArg lamDomain piDomain substitution compiler
        obstruction transport routes provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hBeta
  cases hAppArg
  cases hLamDomain
  cases hPiDomain
  cases hSubstitution
  cases hCompiler
  cases hObstruction
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hName
  rfl

def subjectReductionDischargeToEventFlow : SubjectReductionDischargeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionDischargeUp.mk beta appArg lamDomain piDomain substitution compiler
      obstruction transport routes provenance name =>
      [[BMark.b0],
        subjectReductionDischargeEncodeBHist beta,
        [BMark.b1, BMark.b0],
        subjectReductionDischargeEncodeBHist appArg,
        [BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeEncodeBHist lamDomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeEncodeBHist piDomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeEncodeBHist substitution,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeEncodeBHist compiler,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subjectReductionDischargeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        subjectReductionDischargeEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeEncodeBHist name]

def subjectReductionDischargeFromEventFlow :
    EventFlow → Option SubjectReductionDischargeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | beta :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | appArg :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | lamDomain :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | piDomain :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | substitution :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | compiler :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | obstruction :: rest13 =>
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
                                                                                                (SubjectReductionDischargeUp.mk
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    beta)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    appArg)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    lamDomain)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    piDomain)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    substitution)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    compiler)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    obstruction)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    transport)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    routes)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    provenance)
                                                                                                  (subjectReductionDischargeDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem subjectReductionDischarge_round_trip :
    ∀ x : SubjectReductionDischargeUp,
      subjectReductionDischargeFromEventFlow
          (subjectReductionDischargeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk beta appArg lamDomain piDomain substitution compiler obstruction transport routes
      provenance name =>
      change
        some
          (SubjectReductionDischargeUp.mk
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist beta))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist appArg))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist lamDomain))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist piDomain))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist substitution))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist compiler))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist obstruction))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist transport))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist routes))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist provenance))
            (subjectReductionDischargeDecodeBHist
              (subjectReductionDischargeEncodeBHist name))) =
          some
            (SubjectReductionDischargeUp.mk beta appArg lamDomain piDomain substitution
              compiler obstruction transport routes provenance name)
      exact
        congrArg some
          (subjectReductionDischarge_mk_congr
            (subjectReductionDischargeDecode_encode_bhist beta)
            (subjectReductionDischargeDecode_encode_bhist appArg)
            (subjectReductionDischargeDecode_encode_bhist lamDomain)
            (subjectReductionDischargeDecode_encode_bhist piDomain)
            (subjectReductionDischargeDecode_encode_bhist substitution)
            (subjectReductionDischargeDecode_encode_bhist compiler)
            (subjectReductionDischargeDecode_encode_bhist obstruction)
            (subjectReductionDischargeDecode_encode_bhist transport)
            (subjectReductionDischargeDecode_encode_bhist routes)
            (subjectReductionDischargeDecode_encode_bhist provenance)
            (subjectReductionDischargeDecode_encode_bhist name))

private theorem subjectReductionDischargeToEventFlow_injective
    {x y : SubjectReductionDischargeUp} :
    subjectReductionDischargeToEventFlow x = subjectReductionDischargeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionDischargeFromEventFlow (subjectReductionDischargeToEventFlow x) =
        subjectReductionDischargeFromEventFlow (subjectReductionDischargeToEventFlow y) :=
    congrArg subjectReductionDischargeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectReductionDischarge_round_trip x).symm
      (Eq.trans hread (subjectReductionDischarge_round_trip y)))

instance subjectReductionDischargeBHistCarrier : BHistCarrier SubjectReductionDischargeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionDischargeToEventFlow
  fromEventFlow := subjectReductionDischargeFromEventFlow

instance subjectReductionDischargeChapterTasteGate :
    ChapterTasteGate SubjectReductionDischargeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subjectReductionDischargeFromEventFlow
          (subjectReductionDischargeToEventFlow x) =
        some x
    exact subjectReductionDischarge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectReductionDischargeToEventFlow_injective heq)

instance subjectReductionDischargeFieldFaithful :
    FieldFaithful SubjectReductionDischargeUp where
  fields := fun x =>
    match x with
    | SubjectReductionDischargeUp.mk beta appArg lamDomain piDomain substitution compiler
        obstruction transport routes provenance name =>
        [beta, appArg, lamDomain, piDomain, substitution, compiler, obstruction, transport,
          routes, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk beta₁ appArg₁ lamDomain₁ piDomain₁ substitution₁ compiler₁ obstruction₁
        transport₁ routes₁ provenance₁ name₁ =>
      cases y with
      | mk beta₂ appArg₂ lamDomain₂ piDomain₂ substitution₂ compiler₂ obstruction₂
          transport₂ routes₂ provenance₂ name₂ =>
        injection h with hBeta tail1
        injection tail1 with hAppArg tail2
        injection tail2 with hLamDomain tail3
        injection tail3 with hPiDomain tail4
        injection tail4 with hSubstitution tail5
        injection tail5 with hCompiler tail6
        injection tail6 with hObstruction tail7
        injection tail7 with hTransport tail8
        injection tail8 with hRoutes tail9
        injection tail9 with hProvenance tail10
        injection tail10 with hName _
        cases hBeta
        cases hAppArg
        cases hLamDomain
        cases hPiDomain
        cases hSubstitution
        cases hCompiler
        cases hObstruction
        cases hTransport
        cases hRoutes
        cases hProvenance
        cases hName
        rfl

theorem SubjectReductionDischargeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      subjectReductionDischargeDecodeBHist (subjectReductionDischargeEncodeBHist h) = h) ∧
      (∀ x : SubjectReductionDischargeUp,
        subjectReductionDischargeFromEventFlow (subjectReductionDischargeToEventFlow x) =
          some x) ∧
        (∀ x y : SubjectReductionDischargeUp,
          subjectReductionDischargeToEventFlow x =
              subjectReductionDischargeToEventFlow y →
            x = y) ∧
          subjectReductionDischargeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    And.intro subjectReductionDischargeDecode_encode_bhist
      (And.intro subjectReductionDischarge_round_trip
        (And.intro
          (fun x y heq => subjectReductionDischargeToEventFlow_injective heq)
          rfl))

end BEDC.Derived.SubjectReductionDischargeUp
