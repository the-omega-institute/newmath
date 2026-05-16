import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_dependency_scope [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead transportRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      Cont graph landing landingRead →
        Cont landingRead transport transportRead →
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
            UnaryHistory landing ∧ UnaryHistory transport ∧ UnaryHistory landingRead ∧
              UnaryHistory transportRead ∧ Cont source graph landing ∧
                Cont graph landing landingRead ∧ Cont landingRead transport transportRead ∧
                  hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame ProbeBundle Pkg
  intro carrier graphLandingRead landingReadTransportRead
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, _routesUnary,
    transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_cont_closed graphUnary landingUnary graphLandingRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed landingReadUnary transportUnary landingReadTransportRead
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, transportUnary,
      landingReadUnary, transportReadUnary, sourceGraphLanding, graphLandingRead,
      landingReadTransportRead, certMatchesEndpoint, certPkg⟩

end BEDC.Derived.CertificateCompilerUp
