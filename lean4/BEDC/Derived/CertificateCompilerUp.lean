import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CertificateCompilerCarrier [AskSetup] [PackageSetup]
    (source target graph landing routes transport provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧ UnaryHistory landing ∧
    UnaryHistory routes ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont source graph landing ∧ Cont landing routes target ∧ Cont provenance target cert ∧
        hsame cert (append provenance target) ∧ PkgSig bundle cert pkg

theorem CertificateCompilerCarrier_target_endpoint_route [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert targetEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame targetEndpoint target ->
        UnaryHistory targetEndpoint ∧ UnaryHistory graph ∧ UnaryHistory landing ∧
          Cont source graph landing ∧ Cont landing routes target ∧
            hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier endpointSame
  obtain ⟨_sourceUnary, targetUnary, graphUnary, landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have targetEndpointUnary : UnaryHistory targetEndpoint :=
    unary_transport targetUnary (hsame_symm endpointSame)
  exact
    ⟨targetEndpointUnary, graphUnary, landingUnary, sourceGraphLanding, landingRoutesTarget,
      certMatchesEndpoint, certPkg⟩

theorem CertificateCompilerCarrier_root_classifier_transport_obligation [AskSetup]
    [PackageSetup]
    {source target graph landing routes transport provenance cert targetTransport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      Cont graph transport targetTransport ->
        UnaryHistory transport ∧ UnaryHistory targetTransport ∧
          Cont graph transport targetTransport ∧ Cont landing routes target ∧
            hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier graphTransportTarget
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, _landingUnary, _routesUnary,
    transportUnary, _provenanceUnary, _sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have targetTransportUnary : UnaryHistory targetTransport :=
    unary_cont_closed graphUnary transportUnary graphTransportTarget
  exact
    ⟨transportUnary, targetTransportUnary, graphTransportTarget, landingRoutesTarget,
      certMatchesEndpoint, certPkg⟩

theorem CertificateCompilerCarrier_root_landing_obligation [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame landingRead landing ->
        UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
          UnaryHistory landingRead ∧ Cont source graph landing ∧
            hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier landingSame
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_transport_symm landingUnary landingSame
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingReadUnary, sourceGraphLanding,
      certMatchesEndpoint, certPkg⟩

theorem CertificateCompilerCarrier_bridge_rows_nonescape [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert targetEndpoint certEndpoint :
      BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame targetEndpoint target ->
        hsame cert certEndpoint ->
          UnaryHistory targetEndpoint ∧ UnaryHistory graph ∧ UnaryHistory landing ∧
            UnaryHistory routes ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
              UnaryHistory certEndpoint ∧ Cont source graph landing ∧
                Cont landing routes target ∧ Cont provenance target cert ∧
                  hsame certEndpoint (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier endpointSame certEndpointSame
  obtain ⟨_sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have targetEndpointUnary : UnaryHistory targetEndpoint :=
    unary_transport targetUnary (hsame_symm endpointSame)
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have certEndpointUnary : UnaryHistory certEndpoint :=
    unary_transport certUnary certEndpointSame
  have certEndpointMatches : hsame certEndpoint (append provenance target) :=
    hsame_trans (hsame_symm certEndpointSame) certMatchesEndpoint
  exact
    ⟨targetEndpointUnary, graphUnary, landingUnary, routesUnary, transportUnary,
      provenanceUnary, certEndpointUnary, sourceGraphLanding, landingRoutesTarget,
        provenanceTargetCert, certEndpointMatches, certPkg⟩

theorem CertificateCompilerCarrier_root_continuation_route_obligation [AskSetup]
    [PackageSetup]
    {source target graph landing routes transport provenance cert routeEndpoint certEndpoint :
      BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame routes routeEndpoint ->
        hsame cert certEndpoint ->
          UnaryHistory routeEndpoint ∧ UnaryHistory certEndpoint ∧
            Cont landing routes target ∧ Cont provenance target cert ∧
              hsame certEndpoint (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier routeEndpointSame certEndpointSame
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _landingUnary, routesUnary,
    _transportUnary, provenanceUnary, _sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have routeEndpointUnary : UnaryHistory routeEndpoint :=
    unary_transport routesUnary routeEndpointSame
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have certEndpointUnary : UnaryHistory certEndpoint :=
    unary_transport certUnary certEndpointSame
  have certEndpointMatches : hsame certEndpoint (append provenance target) :=
    hsame_trans (hsame_symm certEndpointSame) certMatchesEndpoint
  exact
    ⟨routeEndpointUnary, certEndpointUnary, landingRoutesTarget, provenanceTargetCert,
      certEndpointMatches, certPkg⟩

theorem CertificateCompilerCarrier_bridge_schema_handoff [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame cert bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont provenance target row ∧ Cont source graph landing ∧
              Cont landing routes target)
            (fun row : BHist => PkgSig bundle row pkg ∧ hsame row (append provenance target))
            (fun row row' : BHist => hsame row row') := by
  intro carrier certBridgeRead bridgePkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _landingUnary, _routesUnary,
    _transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_transport certUnary certBridgeRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeReadUnary, bridgePkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      have certRow : hsame cert row :=
        hsame_trans certBridgeRead (hsame_symm sourceRow.left)
      exact
        ⟨cont_result_hsame_transport provenanceTargetCert certRow, sourceGraphLanding,
          landingRoutesTarget⟩
    ledger_sound := by
      intro row sourceRow
      have bridgeCert : hsame bridgeRead cert :=
        hsame_symm certBridgeRead
      have rowEndpoint : hsame row (append provenance target) :=
        hsame_trans sourceRow.left (hsame_trans bridgeCert certMatchesEndpoint)
      exact ⟨sourceRow.right.right, rowEndpoint⟩
  }

end BEDC.Derived.CertificateCompilerUp
