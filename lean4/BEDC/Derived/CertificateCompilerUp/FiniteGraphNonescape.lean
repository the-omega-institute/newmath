import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_finite_graph_nonescape
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert edge
        edge' bundle pkg →
      Cont graph landing exported →
        PkgSig bundle exported pkg →
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
            UnaryHistory landing ∧ UnaryHistory exported ∧ hsame edge edge' ∧
              Cont source graph landing ∧ Cont graph edge landing ∧
                Cont graph edge' landing ∧ Cont graph landing exported ∧
                  hsame cert (append provenance target) ∧ PkgSig bundle cert pkg ∧
                    PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro classifier graphLandingExported exportedPkg
  obtain ⟨carrier, _edgeUnary, _edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', _landingRoutesTarget'⟩ := classifier
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed graphUnary landingUnary graphLandingExported
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, exportedUnary, edgeSame,
      sourceGraphLanding, graphEdgeLanding, graphEdgeLanding', graphLandingExported,
      certMatchesEndpoint, certPkg, exportedPkg⟩

end BEDC.Derived.CertificateCompilerUp
