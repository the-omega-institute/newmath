import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_endpoint_certificate_availability [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      Cont source graph landing ->
        hsame endpointRead (append source target) ->
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
            UnaryHistory landing ∧ Cont source graph landing ∧ Cont landing routes target ∧
              hsame endpointRead (append source target) ∧
                hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier sourceGraphLandingRead endpointReadSame
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, _sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, sourceGraphLandingRead,
      landingRoutesTarget, endpointReadSame, certMatchesEndpoint, certPkg⟩

end BEDC.Derived.CertificateCompilerUp
