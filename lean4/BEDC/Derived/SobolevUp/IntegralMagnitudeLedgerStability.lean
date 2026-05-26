import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_integral_magnitude_ledger_stability [AskSetup] [PackageSetup]
    {domain metricBase codomain integralRow gradientRow transport replay provenance cert
      magnitudeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain metricBase codomain integralRow gradientRow transport replay provenance
        cert bundle pkg ->
      Cont domain integralRow magnitudeRead ->
        PkgSig bundle magnitudeRead pkg ->
          UnaryHistory domain ∧ UnaryHistory integralRow ∧ UnaryHistory magnitudeRead ∧
            Cont domain integralRow magnitudeRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle magnitudeRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier domainIntegralMagnitude magnitudePkg
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, integralUnary, _gradientUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _certUnary, _domainBaseCodomain,
    _codomainIntegralGradient, _gradientTransportReplay, _replayProvenanceCert,
    provenancePkg⟩ := carrier
  have magnitudeUnary : UnaryHistory magnitudeRead :=
    unary_cont_closed domainUnary integralUnary domainIntegralMagnitude
  exact
    ⟨domainUnary, integralUnary, magnitudeUnary, domainIntegralMagnitude, provenancePkg,
      magnitudePkg⟩

end BEDC.Derived.SobolevUp
