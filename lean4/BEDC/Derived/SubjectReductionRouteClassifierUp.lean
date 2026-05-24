import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionRouteClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubjectReductionRouteClassifierCarrier [AskSetup] [PackageSetup]
    (beta app lambda pi routeKind invocation consumer transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  UnaryHistory beta ∧ UnaryHistory app ∧ UnaryHistory lambda ∧ UnaryHistory pi ∧
    UnaryHistory routeKind ∧ UnaryHistory invocation ∧ UnaryHistory consumer ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont beta app routeKind ∧ Cont lambda pi transport ∧
          Cont invocation consumer route ∧ hsame route routeKind ∧
            hsame route provenance ∧ PkgSig bundle route pkg

theorem SubjectReductionRouteClassifierCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {beta app lambda pi routeKind invocation consumer transport route provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionRouteClassifierCarrier beta app lambda pi routeKind invocation consumer
        transport route provenance name bundle pkg ->
      Cont invocation consumer endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist =>
                SubjectReductionRouteClassifierCarrier beta app lambda pi routeKind invocation
                  consumer transport route provenance name bundle pkg ∧ hsame row endpoint)
              (fun row : BHist => hsame row routeKind)
              (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory beta ∧ UnaryHistory app ∧ UnaryHistory lambda ∧ UnaryHistory pi ∧
              UnaryHistory endpoint ∧ Cont beta app routeKind ∧
                Cont invocation consumer endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert
  intro hCarrier endpointRoute endpointPkg
  have carrierPacket := hCarrier
  obtain ⟨betaUnary, appUnary, lambdaUnary, piUnary, _routeKindUnary, invocationUnary,
    consumerUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, betaAppRouteKind,
    _lambdaPiTransport, invocationConsumerRoute, routeKindReadback, provenanceReadback,
    _carrierPkg⟩ := carrierPacket
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed invocationUnary consumerUnary endpointRoute
  have endpointRouteKind : hsame endpoint routeKind :=
    hsame_trans (cont_deterministic endpointRoute invocationConsumerRoute) routeKindReadback
  have endpointProvenance : hsame endpoint provenance :=
    hsame_trans (cont_deterministic endpointRoute invocationConsumerRoute) provenanceReadback
  have sourceAtEndpoint :
      (fun row : BHist =>
    SubjectReductionRouteClassifierCarrier beta app lambda pi routeKind invocation consumer
            transport route provenance name bundle pkg ∧ hsame row endpoint) endpoint :=
    And.intro hCarrier (hsame_refl endpoint)
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          SubjectReductionRouteClassifierCarrier beta app lambda pi routeKind invocation consumer
              transport route provenance name bundle pkg ∧ hsame row endpoint)
        (fun row : BHist => hsame row routeKind)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact hsame_trans sourceRow.right endpointRouteKind
    ledger_sound := by
      intro _row sourceRow
      exact And.intro (hsame_trans sourceRow.right endpointProvenance) endpointPkg
  }
  exact
    And.intro cert
      (And.intro betaUnary
        (And.intro appUnary
          (And.intro lambdaUnary
            (And.intro piUnary
              (And.intro endpointUnary
                (And.intro betaAppRouteKind endpointRoute))))))

theorem SubjectReductionRouteClassifierCarrier_consumer_nonescape [AskSetup] [PackageSetup]
    {beta app lambda pi routeKind invocation consumer transport route provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionRouteClassifierCarrier beta app lambda pi routeKind invocation consumer
        transport route provenance name bundle pkg →
      Cont invocation consumer endpoint →
        PkgSig bundle endpoint pkg →
          UnaryHistory endpoint ∧ hsame endpoint routeKind ∧ hsame endpoint provenance ∧
            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro hCarrier endpointRoute endpointPkg
  obtain ⟨_betaUnary, _appUnary, _lambdaUnary, _piUnary, _routeKindUnary, invocationUnary,
    consumerUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _betaAppRouteKind, _lambdaPiTransport, invocationConsumerRoute, routeKindReadback,
    provenanceReadback, _carrierPkg⟩ := hCarrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed invocationUnary consumerUnary endpointRoute
  have endpointRouteKind : hsame endpoint routeKind :=
    hsame_trans (cont_deterministic endpointRoute invocationConsumerRoute) routeKindReadback
  have endpointProvenance : hsame endpoint provenance :=
    hsame_trans (cont_deterministic endpointRoute invocationConsumerRoute) provenanceReadback
  exact
    And.intro endpointUnary
      (And.intro endpointRouteKind
        (And.intro endpointProvenance endpointPkg))

theorem SubjectReductionRouteClassifierCarrier_route_kind_coverage [AskSetup] [PackageSetup]
    {beta app lambda pi routeKind invocation consumer transport route provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionRouteClassifierCarrier beta app lambda pi routeKind invocation consumer
        transport route provenance name bundle pkg →
      Cont invocation consumer endpoint →
        PkgSig bundle endpoint pkg →
          UnaryHistory routeKind ∧ hsame endpoint routeKind ∧
            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro hCarrier endpointRoute endpointPkg
  obtain ⟨_betaUnary, _appUnary, _lambdaUnary, _piUnary, routeKindUnary,
    _invocationUnary, _consumerUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, _betaAppRouteKind, _lambdaPiTransport, invocationConsumerRoute,
    routeKindReadback, _provenanceReadback, _carrierPkg⟩ := hCarrier
  have endpointRouteReadback : hsame endpoint route :=
    cont_deterministic endpointRoute invocationConsumerRoute
  exact
    ⟨routeKindUnary, hsame_trans endpointRouteReadback routeKindReadback, endpointPkg⟩

theorem SubjectReductionRouteClassifierCarrier_invocation_payload_inversion [AskSetup]
    [PackageSetup]
    {beta app lambda pi routeKind invocation consumer transport route provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionRouteClassifierCarrier beta app lambda pi routeKind invocation consumer
        transport route provenance name bundle pkg ->
      Cont invocation consumer endpoint ->
        hsame endpoint routeKind ∧ hsame endpoint provenance := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro hCarrier endpointRoute
  obtain ⟨_betaUnary, _appUnary, _lambdaUnary, _piUnary, _routeKindUnary,
    _invocationUnary, _consumerUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, _betaAppRouteKind, _lambdaPiTransport, invocationConsumerRoute,
    routeKindReadback, provenanceReadback, _carrierPkg⟩ := hCarrier
  have endpointRouteReadback : hsame endpoint route :=
    cont_deterministic endpointRoute invocationConsumerRoute
  exact And.intro
    (hsame_trans endpointRouteReadback routeKindReadback)
    (hsame_trans endpointRouteReadback provenanceReadback)

theorem SubjectReductionRouteClassifierCarrier_audit_handoff_totality [AskSetup]
    [PackageSetup]
    {beta app lambda pi routeKind invocation consumer transport route provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionRouteClassifierCarrier beta app lambda pi routeKind invocation consumer
        transport route provenance name bundle pkg ->
      Cont invocation consumer endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory beta ∧ UnaryHistory app ∧ UnaryHistory lambda ∧ UnaryHistory pi ∧
            UnaryHistory endpoint ∧ hsame endpoint routeKind ∧ hsame endpoint provenance ∧
              Cont beta app routeKind ∧ Cont invocation consumer endpoint ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro hCarrier endpointRoute endpointPkg
  obtain ⟨betaUnary, appUnary, lambdaUnary, piUnary, _routeKindUnary, invocationUnary,
    consumerUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    betaAppRouteKind, _lambdaPiTransport, invocationConsumerRoute, routeKindReadback,
    provenanceReadback, _carrierPkg⟩ := hCarrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed invocationUnary consumerUnary endpointRoute
  have endpointRouteKind : hsame endpoint routeKind :=
    hsame_trans (cont_deterministic endpointRoute invocationConsumerRoute) routeKindReadback
  have endpointProvenance : hsame endpoint provenance :=
    hsame_trans (cont_deterministic endpointRoute invocationConsumerRoute) provenanceReadback
  exact
    ⟨betaUnary, appUnary, lambdaUnary, piUnary, endpointUnary, endpointRouteKind,
      endpointProvenance, betaAppRouteKind, endpointRoute, endpointPkg⟩

end BEDC.Derived.SubjectReductionRouteClassifierUp
