import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_source_target_landing_exhaustion [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert sourceRead targetRead
      landingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame sourceRead source ->
        hsame targetRead target ->
          Cont graph landing landingRead ->
            Cont landingRead routes targetRead ->
              PkgSig bundle landingRead pkg ->
                UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧ UnaryHistory graph ∧
                  UnaryHistory landing ∧ UnaryHistory landingRead ∧
                    Cont source graph landing ∧ Cont graph landing landingRead ∧
                      Cont landingRead routes targetRead ∧
                        hsame cert (append provenance target) ∧ PkgSig bundle cert pkg ∧
                          PkgSig bundle landingRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier sourceSame targetSame graphLandingRead landingRoutesTargetRead landingReadPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_transport_symm sourceUnary sourceSame
  have targetReadUnary : UnaryHistory targetRead :=
    unary_transport_symm targetUnary targetSame
  have landingReadUnary : UnaryHistory landingRead :=
    unary_cont_closed graphUnary landingUnary graphLandingRead
  exact
    ⟨sourceReadUnary, targetReadUnary, graphUnary, landingUnary, landingReadUnary,
      sourceGraphLanding, graphLandingRead, landingRoutesTargetRead, certMatchesEndpoint,
      certPkg, landingReadPkg⟩

end BEDC.Derived.CertificateCompilerUp
