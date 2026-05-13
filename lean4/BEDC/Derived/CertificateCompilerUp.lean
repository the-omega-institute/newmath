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

end BEDC.Derived.CertificateCompilerUp
