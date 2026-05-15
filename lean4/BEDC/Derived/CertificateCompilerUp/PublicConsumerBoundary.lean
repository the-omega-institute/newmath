import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_public_consumer_boundary [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead transportRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      Cont graph landing landingRead ->
        Cont landingRead transport transportRead ->
          Cont transportRead routes publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory graph ∧ UnaryHistory landing ∧ UnaryHistory routes ∧
                UnaryHistory transport ∧ UnaryHistory landingRead ∧
                  UnaryHistory transportRead ∧ UnaryHistory publicRead ∧
                    Cont source graph landing ∧ Cont graph landing landingRead ∧
                      Cont landingRead transport transportRead ∧
                        Cont transportRead routes publicRead ∧ PkgSig bundle cert pkg ∧
                          PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier graphLandingRead landingTransportRead transportRoutesPublic publicPkg
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, landingUnary, routesUnary,
    transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, _certMatchesEndpoint, certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_cont_closed graphUnary landingUnary graphLandingRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed landingReadUnary transportUnary landingTransportRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed transportReadUnary routesUnary transportRoutesPublic
  exact
    ⟨graphUnary, landingUnary, routesUnary, transportUnary, landingReadUnary,
      transportReadUnary, publicReadUnary, sourceGraphLanding, graphLandingRead,
      landingTransportRead, transportRoutesPublic, certPkg, publicPkg⟩

end BEDC.Derived.CertificateCompilerUp
