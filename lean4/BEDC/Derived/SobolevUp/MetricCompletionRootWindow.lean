import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_metric_completion_root_window [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      metricRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont base routes metricRead ->
        Cont metricRead provenance completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory base ∧ UnaryHistory routes ∧ UnaryHistory metricRead ∧
              UnaryHistory completionRead ∧ Cont base routes metricRead ∧
                Cont metricRead provenance completionRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier baseRoutesMetric metricProvenanceCompletion completionPkg
  obtain ⟨_domainUnary, baseUnary, _codomainUnary, _magnitudeUnary, _gradientUnary,
    _transportsUnary, routesUnary, provenanceUnary, _localCertUnary, _domainBaseCodomain,
    _codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed baseUnary routesUnary baseRoutesMetric
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary provenanceUnary metricProvenanceCompletion
  exact
    ⟨baseUnary, routesUnary, metricReadUnary, completionReadUnary, baseRoutesMetric,
      metricProvenanceCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.SobolevUp
