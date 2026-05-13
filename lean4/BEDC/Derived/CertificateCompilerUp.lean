import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.CertificateCompilerUp
