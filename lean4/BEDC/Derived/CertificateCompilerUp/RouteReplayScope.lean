import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_route_replay_scope [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg →
      Cont routes provenance replay →
        PkgSig bundle replay pkg →
          UnaryHistory graph ∧ UnaryHistory landing ∧ UnaryHistory routes ∧
            UnaryHistory provenance ∧ UnaryHistory replay ∧ hsame edge edge' ∧
              Cont graph edge landing ∧ Cont graph edge' landing ∧
                Cont landing routes target ∧ Cont routes provenance replay ∧
                  PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro classifier routesProvenanceReplay replayPkg
  obtain ⟨carrier, _edgeUnary, _edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', landingRoutesTarget'⟩ := classifier
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, _certMatchesEndpoint, _certPkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed routesUnary provenanceUnary routesProvenanceReplay
  exact
    ⟨graphUnary, landingUnary, routesUnary, provenanceUnary, replayUnary, edgeSame,
      graphEdgeLanding, graphEdgeLanding', landingRoutesTarget',
      routesProvenanceReplay, replayPkg⟩

end BEDC.Derived.CertificateCompilerUp
