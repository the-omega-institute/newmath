import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CertificateCompilerCarrier_target_endpoint_consumer_determinacy
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' endpoint endpoint'
      composite composite' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg ->
      hsame endpoint target ->
        hsame endpoint' target ->
          Cont edge routes composite ->
            Cont edge' routes composite' ->
              hsame endpoint endpoint' ∧ hsame composite composite' ∧ hsame edge edge' ∧
                Cont graph edge landing ∧ Cont graph edge' landing ∧
                  hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro classifier endpointSame endpointPrimeSame edgeRoutesComposite edgePrimeRoutesComposite
  obtain ⟨carrier, _edgeUnary, _edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', _landingRoutesTarget⟩ := classifier
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, _sourceGraphLanding, _landingRoutesTargetCarrier,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have endpointDeterminacy : hsame endpoint endpoint' :=
    hsame_trans endpointSame (hsame_symm endpointPrimeSame)
  have compositeDeterminacy : hsame composite composite' :=
    cont_respects_hsame edgeSame (hsame_refl routes) edgeRoutesComposite
      edgePrimeRoutesComposite
  exact
    ⟨endpointDeterminacy, compositeDeterminacy, edgeSame, graphEdgeLanding,
      graphEdgeLanding', certMatchesEndpoint, certPkg⟩

end BEDC.Derived.CertificateCompilerUp
