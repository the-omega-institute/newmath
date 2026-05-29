import BEDC.Derived.SeparableMetricUp.TasteGate

namespace BEDC.Derived.SeparableMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparableMetricCarrier_regular_handoff_obligation [AskSetup] [PackageSetup]
    {metric dense windows tolerance readback sealRow transports routes provenance localCert
      handoffExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableMetricCarrier metric dense windows tolerance readback sealRow transports routes
        provenance localCert bundle pkg ->
      Cont dense windows tolerance ->
        Cont tolerance readback handoffExport ->
          PkgSig bundle handoffExport pkg ->
            UnaryHistory dense ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory handoffExport ∧
                Cont dense windows tolerance ∧ Cont tolerance readback handoffExport ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoffExport pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig
  intro carrier denseWindowRoute toleranceReadbackHandoff handoffPkg
  obtain ⟨_metricUnary, denseUnary, windowsUnary, toleranceUnary, readbackUnary,
    _sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
      _carrierDenseRoute, _carrierToleranceRoute, _sealRoute, provenancePkg,
        _localSemantic⟩ := carrier
  have handoffUnary : UnaryHistory handoffExport :=
    unary_cont_closed toleranceUnary readbackUnary toleranceReadbackHandoff
  exact
    ⟨denseUnary, windowsUnary, toleranceUnary, readbackUnary, handoffUnary,
      denseWindowRoute, toleranceReadbackHandoff, provenancePkg, handoffPkg⟩

end BEDC.Derived.SeparableMetricUp
