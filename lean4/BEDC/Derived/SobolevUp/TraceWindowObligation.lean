import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_trace_window_obligation [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      traceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg →
      Cont gradient localCert traceRead →
        PkgSig bundle traceRead pkg →
          UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
            UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
                UnaryHistory traceRead ∧ Cont domain base codomain ∧
                  Cont codomain magnitude gradient ∧ Cont gradient localCert traceRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle traceRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier gradientLocalTrace tracePkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    transportsUnary, routesUnary, provenanceUnary, localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have traceUnary : UnaryHistory traceRead :=
    unary_cont_closed gradientUnary localCertUnary gradientLocalTrace
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
      transportsUnary, routesUnary, provenanceUnary, localCertUnary, traceUnary,
      domainBaseCodomain, codomainMagnitudeGradient, gradientLocalTrace, provenancePkg,
      tracePkg⟩

end BEDC.Derived.SobolevUp
