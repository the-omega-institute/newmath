import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_composite_dependency_scope [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert compositeLanding
      compositeCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      Cont landing graph compositeLanding →
        Cont compositeLanding routes target →
          Cont provenance target compositeCert →
            PkgSig bundle compositeCert pkg →
              UnaryHistory graph ∧ UnaryHistory landing ∧ UnaryHistory routes ∧
                UnaryHistory provenance ∧ UnaryHistory compositeLanding ∧
                  UnaryHistory compositeCert ∧ Cont landing graph compositeLanding ∧
                    Cont compositeLanding routes target ∧ Cont provenance target compositeCert ∧
                      PkgSig bundle compositeCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg
  intro carrier landingGraphComposite compositeRoutesTarget provenanceTargetComposite
    compositePkg
  obtain ⟨_sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, _certMatchesEndpoint, _certPkg⟩ := carrier
  have compositeLandingUnary : UnaryHistory compositeLanding :=
    unary_cont_closed landingUnary graphUnary landingGraphComposite
  have compositeCertUnary : UnaryHistory compositeCert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetComposite
  exact
    ⟨graphUnary, landingUnary, routesUnary, provenanceUnary, compositeLandingUnary,
      compositeCertUnary, landingGraphComposite, compositeRoutesTarget,
      provenanceTargetComposite, compositePkg⟩

end BEDC.Derived.CertificateCompilerUp
