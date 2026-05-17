import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerClassifier_source_target_landing_exhaustion
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' landingRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg →
      Cont graph edge landingRead →
        Cont landingRead routes target →
          PkgSig bundle landingRead pkg →
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
              UnaryHistory edge ∧ UnaryHistory edge' ∧ UnaryHistory landingRead ∧
                Cont source graph landing ∧ Cont graph edge landing ∧
                  Cont graph edge' landing ∧ Cont graph edge landingRead ∧
                    Cont landingRead routes target ∧ hsame edge edge' ∧
                      PkgSig bundle landingRead pkg ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro classifier graphEdgeLandingRead landingReadRoutesTarget landingReadPkg
  obtain ⟨carrier, edgeUnary, edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', _landingRoutesTarget⟩ := classifier
  obtain ⟨sourceUnary, targetUnary, graphUnary, _landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTargetCarrier,
    _provenanceTargetCert, _certMatchesEndpoint, certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_cont_closed graphUnary edgeUnary graphEdgeLandingRead
  exact
    ⟨sourceUnary, targetUnary, graphUnary, edgeUnary, edgeUnary', landingReadUnary,
      sourceGraphLanding, graphEdgeLanding, graphEdgeLanding', graphEdgeLandingRead,
      landingReadRoutesTarget, edgeSame, landingReadPkg, certPkg⟩

end BEDC.Derived.CertificateCompilerUp
