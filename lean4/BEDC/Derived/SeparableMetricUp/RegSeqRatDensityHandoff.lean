import BEDC.Derived.SeparableMetricUp.TasteGate

namespace BEDC.Derived.SeparableMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparableMetricCarrier_regseqrat_density_handoff [AskSetup] [PackageSetup]
    {metric dense windows tolerance readback sealRow transports routes provenance localCert
      densityHandoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableMetricCarrier metric dense windows tolerance readback sealRow transports routes
        provenance localCert bundle pkg →
      Cont dense tolerance densityHandoff →
        PkgSig bundle densityHandoff pkg →
          UnaryHistory dense ∧ UnaryHistory tolerance ∧ UnaryHistory densityHandoff ∧
            Cont dense windows tolerance ∧ Cont dense tolerance densityHandoff ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle densityHandoff pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier denseToleranceHandoff densityHandoffPkg
  obtain ⟨_metricUnary, denseUnary, _windowsUnary, toleranceUnary, _readbackUnary,
    _sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
    denseWindowTolerance, _toleranceReadbackSeal, _sealRouteProvenance, provenancePkg,
    _localCert⟩ := carrier
  have densityHandoffUnary : UnaryHistory densityHandoff :=
    unary_cont_closed denseUnary toleranceUnary denseToleranceHandoff
  exact
    ⟨denseUnary, toleranceUnary, densityHandoffUnary, denseWindowTolerance,
      denseToleranceHandoff, provenancePkg, densityHandoffPkg⟩

end BEDC.Derived.SeparableMetricUp
