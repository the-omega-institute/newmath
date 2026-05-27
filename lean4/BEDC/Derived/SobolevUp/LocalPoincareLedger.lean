import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_local_poincare_ledger [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg →
      Cont magnitude gradient localRead →
        PkgSig bundle localRead pkg →
          ∃ comparisonRead : BHist,
            UnaryHistory comparisonRead ∧
              hsame comparisonRead (append (append magnitude gradient) transports) ∧
                Cont domain base codomain ∧
                  Cont codomain magnitude gradient ∧
                    Cont magnitude gradient localRead ∧
                      Cont gradient transports routes ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle localRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier localRoute localPkg
  obtain ⟨_domainUnary, _baseUnary, _codomainUnary, magnitudeUnary, gradientUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed magnitudeUnary gradientUnary localRoute
  have magnitudeGradientUnary : UnaryHistory (append magnitude gradient) :=
    unary_append_closed magnitudeUnary gradientUnary
  exact
    ⟨append (append magnitude gradient) transports,
      unary_append_closed magnitudeGradientUnary transportsUnary,
      hsame_refl (append (append magnitude gradient) transports), domainBaseCodomain,
      codomainMagnitudeGradient, localRoute, gradientTransportsRoutes, provenancePkg,
      localPkg⟩

end BEDC.Derived.SobolevUp
