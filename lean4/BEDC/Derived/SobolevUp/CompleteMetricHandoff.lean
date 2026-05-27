import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_complete_metric_handoff [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont base provenance completionRead ->
        UnaryHistory completionRead ∧ Cont domain base codomain ∧
          Cont codomain magnitude gradient ∧ Cont routes provenance localCert ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier baseProvenanceCompletion
  rcases carrier with
    ⟨_domainUnary, baseUnary, _codomainUnary, _magnitudeUnary, _gradientUnary,
      _transportsUnary, _routesUnary, provenanceUnary, _localCertUnary, domainBaseCodomain,
      codomainMagnitudeGradient, _gradientTransportsRoutes, routesProvenanceLocalCert,
      provenancePkg⟩
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed baseUnary provenanceUnary baseProvenanceCompletion
  exact
    ⟨completionUnary, domainBaseCodomain, codomainMagnitudeGradient,
      routesProvenanceLocalCert, provenancePkg⟩

end BEDC.Derived.SobolevUp
