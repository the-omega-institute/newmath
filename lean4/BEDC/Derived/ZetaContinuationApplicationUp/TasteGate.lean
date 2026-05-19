import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZetaContinuationApplicationUp : Type where
  | mk :
      (eta functional pole zeroLedger gamma application transport route provenance name : BHist) →
        ZetaContinuationApplicationUp
  deriving DecidableEq

def zetaContinuationApplicationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zetaContinuationApplicationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zetaContinuationApplicationEncodeBHist h

def zetaContinuationApplicationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zetaContinuationApplicationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zetaContinuationApplicationDecodeBHist tail)

private theorem zetaContinuationApplicationDecode_encode_bhist :
    ∀ h : BHist,
      zetaContinuationApplicationDecodeBHist
        (zetaContinuationApplicationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem zetaContinuationApplication_mk_congr
    {eta eta' functional functional' pole pole' zeroLedger zeroLedger' gamma gamma'
      application application' transport transport' route route' provenance provenance'
      name name' : BHist}
    (hEta : eta' = eta)
    (hFunctional : functional' = functional)
    (hPole : pole' = pole)
    (hZeroLedger : zeroLedger' = zeroLedger)
    (hGamma : gamma' = gamma)
    (hApplication : application' = application)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ZetaContinuationApplicationUp.mk eta' functional' pole' zeroLedger' gamma' application'
        transport' route' provenance' name' =
      ZetaContinuationApplicationUp.mk eta functional pole zeroLedger gamma application transport
        route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hEta
  cases hFunctional
  cases hPole
  cases hZeroLedger
  cases hGamma
  cases hApplication
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def zetaContinuationApplicationToEventFlow : ZetaContinuationApplicationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ZetaContinuationApplicationUp.mk eta functional pole zeroLedger gamma application transport
      route provenance name =>
      [[BMark.b0],
        zetaContinuationApplicationEncodeBHist eta,
        [BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist functional,
        [BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist pole,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist zeroLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist gamma,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist application,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        zetaContinuationApplicationEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist name]

def zetaContinuationApplicationFromEventFlow : EventFlow → Option ZetaContinuationApplicationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | eta :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | functional :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | pole :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | zeroLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gamma :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | application :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ZetaContinuationApplicationUp.mk
                                                                                          (zetaContinuationApplicationDecodeBHist eta)
                                                                                          (zetaContinuationApplicationDecodeBHist functional)
                                                                                          (zetaContinuationApplicationDecodeBHist pole)
                                                                                          (zetaContinuationApplicationDecodeBHist zeroLedger)
                                                                                          (zetaContinuationApplicationDecodeBHist gamma)
                                                                                          (zetaContinuationApplicationDecodeBHist application)
                                                                                          (zetaContinuationApplicationDecodeBHist transport)
                                                                                          (zetaContinuationApplicationDecodeBHist route)
                                                                                          (zetaContinuationApplicationDecodeBHist provenance)
                                                                                          (zetaContinuationApplicationDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem zetaContinuationApplication_round_trip :
    ∀ x : ZetaContinuationApplicationUp,
      zetaContinuationApplicationFromEventFlow
        (zetaContinuationApplicationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk eta functional pole zeroLedger gamma application transport route provenance name =>
      change
        some
          (ZetaContinuationApplicationUp.mk
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist eta))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist functional))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist pole))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist zeroLedger))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist gamma))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist application))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist transport))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist route))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist provenance))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist name))) =
          some
            (ZetaContinuationApplicationUp.mk eta functional pole zeroLedger gamma application
              transport route provenance name)
      exact
        congrArg some
          (zetaContinuationApplication_mk_congr
            (zetaContinuationApplicationDecode_encode_bhist eta)
            (zetaContinuationApplicationDecode_encode_bhist functional)
            (zetaContinuationApplicationDecode_encode_bhist pole)
            (zetaContinuationApplicationDecode_encode_bhist zeroLedger)
            (zetaContinuationApplicationDecode_encode_bhist gamma)
            (zetaContinuationApplicationDecode_encode_bhist application)
            (zetaContinuationApplicationDecode_encode_bhist transport)
            (zetaContinuationApplicationDecode_encode_bhist route)
            (zetaContinuationApplicationDecode_encode_bhist provenance)
            (zetaContinuationApplicationDecode_encode_bhist name))

private theorem zetaContinuationApplicationToEventFlow_injective
    {x y : ZetaContinuationApplicationUp} :
    zetaContinuationApplicationToEventFlow x = zetaContinuationApplicationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zetaContinuationApplicationFromEventFlow (zetaContinuationApplicationToEventFlow x) =
        zetaContinuationApplicationFromEventFlow (zetaContinuationApplicationToEventFlow y) :=
    congrArg zetaContinuationApplicationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (zetaContinuationApplication_round_trip x).symm
      (Eq.trans hread (zetaContinuationApplication_round_trip y)))

instance zetaContinuationApplicationBHistCarrier :
    BHistCarrier ZetaContinuationApplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zetaContinuationApplicationToEventFlow
  fromEventFlow := zetaContinuationApplicationFromEventFlow

instance zetaContinuationApplicationChapterTasteGate :
    ChapterTasteGate ZetaContinuationApplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      zetaContinuationApplicationFromEventFlow
        (zetaContinuationApplicationToEventFlow x) = some x
    exact zetaContinuationApplication_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (zetaContinuationApplicationToEventFlow_injective heq)

instance zetaContinuationApplicationFieldFaithful :
    FieldFaithful ZetaContinuationApplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ZetaContinuationApplicationUp.mk eta functional pole zeroLedger gamma application
        transport route provenance name =>
        [eta, functional, pole, zeroLedger, gamma, application, transport, route, provenance,
          name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk eta1 functional1 pole1 zeroLedger1 gamma1 application1 transport1 route1
        provenance1 name1 =>
        cases y with
        | mk eta2 functional2 pole2 zeroLedger2 gamma2 application2 transport2 route2
            provenance2 name2 =>
            cases hfields
            rfl

def taste_gate : ChapterTasteGate ZetaContinuationApplicationUp :=
  zetaContinuationApplicationChapterTasteGate

theorem ZetaContinuationApplicationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      zetaContinuationApplicationDecodeBHist
        (zetaContinuationApplicationEncodeBHist h) = h) ∧
      (∀ x : ZetaContinuationApplicationUp,
        zetaContinuationApplicationFromEventFlow
          (zetaContinuationApplicationToEventFlow x) = some x) ∧
        (∀ x y : ZetaContinuationApplicationUp,
          zetaContinuationApplicationToEventFlow x =
            zetaContinuationApplicationToEventFlow y → x = y) ∧
          zetaContinuationApplicationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact zetaContinuationApplicationDecode_encode_bhist
  · constructor
    · exact zetaContinuationApplication_round_trip
    · constructor
      · intro x y heq
        exact zetaContinuationApplicationToEventFlow_injective heq
      · rfl

def ZetaContinuationApplicationCarrier [AskSetup] [PackageSetup]
    (eta functional pole zeroLedger gamma application transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory eta ∧ UnaryHistory functional ∧ UnaryHistory pole ∧
    UnaryHistory zeroLedger ∧ UnaryHistory gamma ∧ UnaryHistory application ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont transport replay provenance ∧
          Cont eta functional application ∧ Cont gamma application replay ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem ZetaContinuationApplicationCarrier_carrier_source_obligation [AskSetup]
    [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      hsame sourceRead eta →
        UnaryHistory sourceRead ∧ UnaryHistory eta ∧ UnaryHistory gamma ∧
          UnaryHistory application ∧ UnaryHistory replay ∧ Cont eta functional application ∧
            Cont gamma application replay ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameSourceEta
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, etaFunctionalApplication, gammaApplicationReplay, provenancePkg,
    _namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_transport etaUnary (hsame_symm sameSourceEta)
  exact
    ⟨sourceReadUnary,
      etaUnary,
      gammaUnary,
      applicationUnary,
      replayUnary,
      etaFunctionalApplication,
      gammaApplicationReplay,
      provenancePkg⟩

theorem ZetaContinuationApplicationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application
              transport replay provenance name bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          hsame row provenance ∧ PkgSig bundle provenance pkg)
        (fun _row : BHist =>
          UnaryHistory eta ∧ UnaryHistory functional ∧ UnaryHistory pole ∧
            UnaryHistory zeroLedger ∧ UnaryHistory gamma ∧ UnaryHistory application ∧
              UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
                UnaryHistory name)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg NameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨etaUnary, functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    applicationUnary, transportUnary, replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay, provenancePkg,
    _namePkg⟩ := carrier
  constructor
  · constructor
    · exact Exists.intro provenance ⟨carrierWitness, hsame_refl provenance⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other same
      exact hsame_symm same
    · intro _row _other _third sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other same source
      exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
  · intro _row source
    exact ⟨source.right, provenancePkg⟩
  · intro _row _source
    exact
      ⟨etaUnary, functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary, applicationUnary,
        transportUnary, replayUnary, provenanceUnary, nameUnary⟩

theorem ZetaContinuationApplicationCarrier_route_totality [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont application replay consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory eta ∧ UnaryHistory functional ∧ UnaryHistory gamma ∧
            UnaryHistory application ∧ UnaryHistory replay ∧ UnaryHistory consumer ∧
              Cont eta functional application ∧ Cont gamma application replay ∧
                Cont application replay consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier applicationReplayConsumer consumerPkg
  obtain ⟨etaUnary, functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, etaFunctionalApplication, gammaApplicationReplay, provenancePkg,
    _namePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed applicationUnary replayUnary applicationReplayConsumer
  exact
    ⟨etaUnary,
      functionalUnary,
      gammaUnary,
      applicationUnary,
      replayUnary,
      consumerUnary,
      etaFunctionalApplication,
      gammaApplicationReplay,
      applicationReplayConsumer,
      provenancePkg,
      consumerPkg⟩

theorem ZetaContinuationApplicationCarrier_root_source_readiness [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name sourceRead
      gammaRead operationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma sourceRead →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            PkgSig bundle operationRead pkg →
              UnaryHistory eta ∧ UnaryHistory gamma ∧ UnaryHistory application ∧
                UnaryHistory sourceRead ∧ UnaryHistory gammaRead ∧
                  UnaryHistory operationRead ∧ Cont eta gamma sourceRead ∧
                    Cont gamma application gammaRead ∧ Cont application replay operationRead ∧
                      Cont eta functional application ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle operationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier etaGammaSource gammaApplicationRead applicationReplayOperation operationPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, etaFunctionalApplication, _gammaApplicationReplay, provenancePkg,
    _namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaSource
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  exact
    ⟨etaUnary,
      gammaUnary,
      applicationUnary,
      sourceReadUnary,
      gammaReadUnary,
      operationReadUnary,
      etaGammaSource,
      gammaApplicationRead,
      applicationReplayOperation,
      etaFunctionalApplication,
      provenancePkg,
      operationPkg⟩

theorem ZetaContinuationApplicationCarrier_componentwise_stability [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name etaRead
      gammaRead operationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      hsame etaRead eta →
        Cont gamma application gammaRead →
          Cont application replay operationRead →
            PkgSig bundle operationRead pkg →
              UnaryHistory etaRead ∧ UnaryHistory eta ∧ UnaryHistory gamma ∧
                UnaryHistory application ∧ UnaryHistory gammaRead ∧
                  UnaryHistory operationRead ∧ Cont eta functional application ∧
                    Cont gamma application gammaRead ∧ Cont application replay operationRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle operationRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle PkgSig
  intro carrier sameEtaRead gammaApplicationRead applicationReplayOperation operationPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have etaReadUnary : UnaryHistory etaRead :=
    unary_transport etaUnary (hsame_symm sameEtaRead)
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have operationReadUnary : UnaryHistory operationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayOperation
  exact
    ⟨etaReadUnary,
      etaUnary,
      gammaUnary,
      applicationUnary,
      gammaReadUnary,
      operationReadUnary,
      etaFunctionalApplication,
      gammaApplicationRead,
      applicationReplayOperation,
      provenancePkg,
      operationPkg⟩

theorem ZetaContinuationApplicationCarrier_ledger_route_obligation [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      poleRead gammaRead applicationRead ledgerRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg ->
      Cont pole zeroLedger poleRead -> Cont gamma application gammaRead ->
        Cont application replay applicationRead -> Cont poleRead gammaRead ledgerRoute ->
          PkgSig bundle ledgerRoute pkg ->
            UnaryHistory pole ∧ UnaryHistory zeroLedger ∧ UnaryHistory gamma ∧
              UnaryHistory application ∧ UnaryHistory poleRead ∧ UnaryHistory gammaRead ∧
                UnaryHistory applicationRead ∧ UnaryHistory ledgerRoute ∧
                  Cont pole zeroLedger poleRead ∧ Cont gamma application gammaRead ∧
                    Cont application replay applicationRead ∧ Cont poleRead gammaRead ledgerRoute ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier poleZeroRead gammaApplicationRead applicationReplayRead readLedgerRoute
    ledgerRoutePkg
  obtain ⟨_etaUnary, _functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have poleReadUnary : UnaryHistory poleRead :=
    unary_cont_closed poleUnary zeroLedgerUnary poleZeroRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have applicationReadUnary : UnaryHistory applicationRead :=
    unary_cont_closed applicationUnary replayUnary applicationReplayRead
  have ledgerRouteUnary : UnaryHistory ledgerRoute :=
    unary_cont_closed poleReadUnary gammaReadUnary readLedgerRoute
  exact
    ⟨poleUnary,
      zeroLedgerUnary,
      gammaUnary,
      applicationUnary,
      poleReadUnary,
      gammaReadUnary,
      applicationReadUnary,
      ledgerRouteUnary,
      poleZeroRead,
      gammaApplicationRead,
      applicationReplayRead,
      readLedgerRoute,
      provenancePkg,
      ledgerRoutePkg⟩

theorem ZetaContinuationApplicationCarrier_boundary_ledger_nonescape [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name poleRead
      zeroRead gammaRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont pole zeroLedger poleRead →
        Cont zeroLedger gamma zeroRead →
          Cont gamma application gammaRead →
            Cont provenance name boundaryRead →
              PkgSig bundle boundaryRead pkg →
                UnaryHistory pole ∧ UnaryHistory zeroLedger ∧ UnaryHistory gamma ∧
                  UnaryHistory poleRead ∧ UnaryHistory zeroRead ∧ UnaryHistory gammaRead ∧
                    UnaryHistory boundaryRead ∧ Cont pole zeroLedger poleRead ∧
                      Cont zeroLedger gamma zeroRead ∧ Cont gamma application gammaRead ∧
                        Cont provenance name boundaryRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier poleZeroRead zeroGammaRead gammaApplicationRead provenanceNameRead
    boundaryPkg
  obtain ⟨_etaUnary, _functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have poleReadUnary : UnaryHistory poleRead :=
    unary_cont_closed poleUnary zeroLedgerUnary poleZeroRead
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroLedgerUnary gammaUnary zeroGammaRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameRead
  exact
    ⟨poleUnary, zeroLedgerUnary, gammaUnary, poleReadUnary, zeroReadUnary,
      gammaReadUnary, boundaryReadUnary, poleZeroRead, zeroGammaRead, gammaApplicationRead,
      provenanceNameRead, provenancePkg, boundaryPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
