import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_kernel_morphism_route_coverage [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' kernelRoute :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg ->
      Cont graph kernelRoute target ->
        UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
          UnaryHistory landing ∧ UnaryHistory routes ∧ UnaryHistory transport ∧
            UnaryHistory provenance ∧ UnaryHistory edge ∧ UnaryHistory edge' ∧
              hsame edge edge' ∧ Cont source graph landing ∧ Cont graph edge landing ∧
                Cont graph edge' landing ∧ Cont landing routes target ∧
                  Cont graph kernelRoute target ∧ hsame cert (append provenance target) ∧
                    PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro classifier graphKernelTarget
  obtain ⟨carrier, edgeUnary, edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', landingRoutesTarget'⟩ := classifier
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    transportUnary, provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary, transportUnary,
      provenanceUnary, edgeUnary, edgeUnary', edgeSame, sourceGraphLanding,
      graphEdgeLanding, graphEdgeLanding', landingRoutesTarget', graphKernelTarget,
      certMatchesEndpoint, certPkg⟩

end BEDC.Derived.CertificateCompilerUp
