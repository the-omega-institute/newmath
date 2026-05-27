import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_hilbert_completion_descent [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      hilbertRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg →
      Cont codomain magnitude hilbertRead →
        Cont hilbertRead provenance completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory hilbertRead ∧ UnaryHistory completionRead ∧
              Cont domain base codomain ∧ Cont codomain magnitude hilbertRead ∧
                Cont codomain magnitude gradient ∧ Cont hilbertRead provenance completionRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier codomainMagnitudeHilbert hilbertProvenanceCompletion completionPkg
  rcases carrier with
    ⟨_domainUnary, _baseUnary, codomainUnary, magnitudeUnary, _gradientUnary,
      _transportsUnary, _routesUnary, provenanceUnary, _localCertUnary, domainBaseCodomain,
      codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
      provenancePkg⟩
  have hilbertUnary : UnaryHistory hilbertRead :=
    unary_cont_closed codomainUnary magnitudeUnary codomainMagnitudeHilbert
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed hilbertUnary provenanceUnary hilbertProvenanceCompletion
  exact
    ⟨hilbertUnary, completionUnary, domainBaseCodomain, codomainMagnitudeHilbert,
      codomainMagnitudeGradient, hilbertProvenanceCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.SobolevUp
