import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionDischargeSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def SubjectReductionDischargeSocketPacket [AskSetup] [PackageSetup]
    (beta appArg lamDomain piDomain transport routes ledger name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory lamDomain ∧
    UnaryHistory piDomain ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
      UnaryHistory ledger ∧ UnaryHistory name ∧ Cont beta appArg transport ∧
        Cont lamDomain piDomain routes ∧ Cont transport routes ledger ∧
          Cont ledger name beta ∧ PkgSig bundle name pkg

theorem SubjectReductionDischargeSocketPacket_nonescape [AskSetup] [PackageSetup]
    {beta appArg lamDomain piDomain transport routes ledger name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeSocketPacket beta appArg lamDomain piDomain transport routes
        ledger name bundle pkg ->
      Cont beta appArg consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory consumer ∧
            Cont beta appArg consumer ∧ PkgSig bundle consumer pkg ∧
              PkgSig bundle name pkg := by
  intro packet consumerRoute consumerPkg
  obtain ⟨betaUnary, appArgUnary, _lamDomainUnary, _piDomainUnary, _transportUnary,
    _routesUnary, _ledgerUnary, _nameUnary, _betaAppTransport, _domainRoute,
    _transportRoutesLedger, _ledgerNameBeta, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed betaUnary appArgUnary consumerRoute
  exact
    ⟨betaUnary, appArgUnary, consumerUnary, consumerRoute, consumerPkg, namePkg⟩

inductive SubjectReductionDischargeSocketUp : Type where
  | mk :
      (beta appArg lamDomain piDomain transport routes ledger name : BHist) →
      SubjectReductionDischargeSocketUp
  deriving DecidableEq

def subjectReductionDischargeSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionDischargeSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionDischargeSocketEncodeBHist h

def subjectReductionDischargeSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionDischargeSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionDischargeSocketDecodeBHist tail)

private theorem subjectReductionDischargeSocketDecode_encode_bhist :
    ∀ h : BHist,
      subjectReductionDischargeSocketDecodeBHist
          (subjectReductionDischargeSocketEncodeBHist h) =
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

private theorem subjectReductionDischargeSocket_mk_congr
    {beta beta' appArg appArg' lamDomain lamDomain' piDomain piDomain' transport
      transport' routes routes' ledger ledger' name name' : BHist}
    (hBeta : beta' = beta)
    (hAppArg : appArg' = appArg)
    (hLamDomain : lamDomain' = lamDomain)
    (hPiDomain : piDomain' = piDomain)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hLedger : ledger' = ledger)
    (hName : name' = name) :
    SubjectReductionDischargeSocketUp.mk beta' appArg' lamDomain' piDomain' transport'
        routes' ledger' name' =
      SubjectReductionDischargeSocketUp.mk beta appArg lamDomain piDomain transport routes
        ledger name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hBeta
  cases hAppArg
  cases hLamDomain
  cases hPiDomain
  cases hTransport
  cases hRoutes
  cases hLedger
  cases hName
  rfl

def subjectReductionDischargeSocketToEventFlow :
    SubjectReductionDischargeSocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionDischargeSocketUp.mk beta appArg lamDomain piDomain transport routes
      ledger name =>
      [[BMark.b0],
        subjectReductionDischargeSocketEncodeBHist beta,
        [BMark.b1, BMark.b0],
        subjectReductionDischargeSocketEncodeBHist appArg,
        [BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeSocketEncodeBHist lamDomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeSocketEncodeBHist piDomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeSocketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeSocketEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionDischargeSocketEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subjectReductionDischargeSocketEncodeBHist name]

def subjectReductionDischargeSocketFromEventFlow :
    EventFlow → Option SubjectReductionDischargeSocketUp
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
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | routes :: rest11 =>
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
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (SubjectReductionDischargeSocketUp.mk
                                                                          (subjectReductionDischargeSocketDecodeBHist
                                                                            beta)
                                                                          (subjectReductionDischargeSocketDecodeBHist
                                                                            appArg)
                                                                          (subjectReductionDischargeSocketDecodeBHist
                                                                            lamDomain)
                                                                          (subjectReductionDischargeSocketDecodeBHist
                                                                            piDomain)
                                                                          (subjectReductionDischargeSocketDecodeBHist
                                                                            transport)
                                                                          (subjectReductionDischargeSocketDecodeBHist
                                                                            routes)
                                                                          (subjectReductionDischargeSocketDecodeBHist
                                                                            ledger)
                                                                          (subjectReductionDischargeSocketDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem subjectReductionDischargeSocket_round_trip :
    ∀ x : SubjectReductionDischargeSocketUp,
      subjectReductionDischargeSocketFromEventFlow
          (subjectReductionDischargeSocketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk beta appArg lamDomain piDomain transport routes ledger name =>
      change
        some
          (SubjectReductionDischargeSocketUp.mk
            (subjectReductionDischargeSocketDecodeBHist
              (subjectReductionDischargeSocketEncodeBHist beta))
            (subjectReductionDischargeSocketDecodeBHist
              (subjectReductionDischargeSocketEncodeBHist appArg))
            (subjectReductionDischargeSocketDecodeBHist
              (subjectReductionDischargeSocketEncodeBHist lamDomain))
            (subjectReductionDischargeSocketDecodeBHist
              (subjectReductionDischargeSocketEncodeBHist piDomain))
            (subjectReductionDischargeSocketDecodeBHist
              (subjectReductionDischargeSocketEncodeBHist transport))
            (subjectReductionDischargeSocketDecodeBHist
              (subjectReductionDischargeSocketEncodeBHist routes))
            (subjectReductionDischargeSocketDecodeBHist
              (subjectReductionDischargeSocketEncodeBHist ledger))
            (subjectReductionDischargeSocketDecodeBHist
              (subjectReductionDischargeSocketEncodeBHist name))) =
          some
            (SubjectReductionDischargeSocketUp.mk beta appArg lamDomain piDomain transport
              routes ledger name)
      exact
        congrArg some
          (subjectReductionDischargeSocket_mk_congr
            (subjectReductionDischargeSocketDecode_encode_bhist beta)
            (subjectReductionDischargeSocketDecode_encode_bhist appArg)
            (subjectReductionDischargeSocketDecode_encode_bhist lamDomain)
            (subjectReductionDischargeSocketDecode_encode_bhist piDomain)
            (subjectReductionDischargeSocketDecode_encode_bhist transport)
            (subjectReductionDischargeSocketDecode_encode_bhist routes)
            (subjectReductionDischargeSocketDecode_encode_bhist ledger)
            (subjectReductionDischargeSocketDecode_encode_bhist name))

private theorem subjectReductionDischargeSocketToEventFlow_injective
    {x y : SubjectReductionDischargeSocketUp} :
    subjectReductionDischargeSocketToEventFlow x =
        subjectReductionDischargeSocketToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionDischargeSocketFromEventFlow
          (subjectReductionDischargeSocketToEventFlow x) =
        subjectReductionDischargeSocketFromEventFlow
          (subjectReductionDischargeSocketToEventFlow y) :=
    congrArg subjectReductionDischargeSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectReductionDischargeSocket_round_trip x).symm
      (Eq.trans hread (subjectReductionDischargeSocket_round_trip y)))

instance subjectReductionDischargeSocketBHistCarrier :
    BHistCarrier SubjectReductionDischargeSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionDischargeSocketToEventFlow
  fromEventFlow := subjectReductionDischargeSocketFromEventFlow

instance subjectReductionDischargeSocketChapterTasteGate :
    ChapterTasteGate SubjectReductionDischargeSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subjectReductionDischargeSocketFromEventFlow
          (subjectReductionDischargeSocketToEventFlow x) =
        some x
    exact subjectReductionDischargeSocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectReductionDischargeSocketToEventFlow_injective heq)

theorem SubjectReductionDischargeSocketCarrier_namecert_obligations :
    (∀ h : BHist,
      subjectReductionDischargeSocketDecodeBHist
          (subjectReductionDischargeSocketEncodeBHist h) =
        h) ∧
      (∀ x : SubjectReductionDischargeSocketUp,
        subjectReductionDischargeSocketFromEventFlow
            (subjectReductionDischargeSocketToEventFlow x) =
          some x) ∧
        (∀ x y : SubjectReductionDischargeSocketUp,
          subjectReductionDischargeSocketToEventFlow x =
              subjectReductionDischargeSocketToEventFlow y →
            x = y) ∧
          (∀ B A L P H C Q N : BHist,
            Cont B A (append B A) ∧ Cont L P (append L P) ∧ hsame H H ∧ hsame C C ∧
              hsame Q Q ∧ hsame N N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  constructor
  · exact subjectReductionDischargeSocketDecode_encode_bhist
  · constructor
    · exact subjectReductionDischargeSocket_round_trip
    · constructor
      · intro x y heq
        exact subjectReductionDischargeSocketToEventFlow_injective heq
      · intro B A L P H C Q N
        constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · rfl

theorem SubjectReductionDischargeSocketPacket_four_row_ledger_exactness [AskSetup]
    [PackageSetup]
    {beta appArg lamDomain piDomain transport routes ledger name betaRead lamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeSocketPacket beta appArg lamDomain piDomain transport routes
        ledger name bundle pkg →
      Cont beta appArg betaRead →
        Cont lamDomain piDomain lamRead →
          UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory lamDomain ∧
            UnaryHistory piDomain ∧ UnaryHistory betaRead ∧ UnaryHistory lamRead ∧
              Cont beta appArg transport ∧ Cont lamDomain piDomain routes ∧
                Cont transport routes ledger ∧ Cont ledger name beta ∧
                  Cont beta appArg betaRead ∧ Cont lamDomain piDomain lamRead ∧
                    PkgSig bundle name pkg := by
  intro packet betaReadRoute lamReadRoute
  obtain ⟨betaUnary, appArgUnary, lamDomainUnary, piDomainUnary, _transportUnary,
    _routesUnary, _ledgerUnary, _nameUnary, betaAppTransport, domainRoute,
    transportRoutesLedger, ledgerNameBeta, namePkg⟩ := packet
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed betaUnary appArgUnary betaReadRoute
  have lamReadUnary : UnaryHistory lamRead :=
    unary_cont_closed lamDomainUnary piDomainUnary lamReadRoute
  exact
    ⟨betaUnary, appArgUnary, lamDomainUnary, piDomainUnary, betaReadUnary,
      lamReadUnary, betaAppTransport, domainRoute, transportRoutesLedger,
      ledgerNameBeta, betaReadRoute, lamReadRoute, namePkg⟩

end BEDC.Derived.SubjectReductionDischargeSocketUp
