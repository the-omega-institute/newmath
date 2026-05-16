import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerClassifier_edge_classifier_exactness [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' sourceRead
      targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg ->
      hsame sourceRead source ->
        hsame targetRead target ->
          UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧ UnaryHistory graph ∧
            UnaryHistory landing ∧ UnaryHistory edge ∧ UnaryHistory edge' ∧
              hsame edge edge' ∧ Cont source graph landing ∧ Cont graph edge landing ∧
                Cont graph edge' landing ∧ Cont landing routes target ∧
                  hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro classifier sourceSame targetSame
  obtain ⟨carrier, edgeUnary, edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', landingRoutesTarget'⟩ := classifier
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_transport_symm sourceUnary sourceSame
  have targetReadUnary : UnaryHistory targetRead :=
    unary_transport_symm targetUnary targetSame
  exact
    ⟨sourceReadUnary, targetReadUnary, graphUnary, landingUnary, edgeUnary, edgeUnary',
      edgeSame, sourceGraphLanding, graphEdgeLanding, graphEdgeLanding',
      landingRoutesTarget', certMatchesEndpoint, certPkg⟩

end BEDC.Derived.CertificateCompilerUp
