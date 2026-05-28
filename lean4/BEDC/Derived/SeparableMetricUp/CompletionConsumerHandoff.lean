import BEDC.Derived.SeparableMetricUp.TasteGate

namespace BEDC.Derived.SeparableMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparableMetricCarrier_completion_consumer_handoff [AskSetup] [PackageSetup]
    {metric dense windows tolerance readback sealRow transports routes provenance localCert
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableMetricCarrier metric dense windows tolerance readback sealRow transports routes
        provenance localCert bundle pkg ->
      Cont readback sealRow completionRead ->
        PkgSig bundle completionRead pkg ->
          UnaryHistory dense ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory completionRead ∧
              Cont dense windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont readback sealRow completionRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier readbackSealCompletion completionPkg
  obtain ⟨_metricUnary, denseUnary, windowsUnary, toleranceUnary, readbackUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
    denseWindowRoute, toleranceReadbackRoute, _sealRoute, provenancePkg,
    _localSemantic⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed readbackUnary sealRowUnary readbackSealCompletion
  exact
    ⟨denseUnary, windowsUnary, toleranceUnary, readbackUnary, sealRowUnary, completionUnary,
      denseWindowRoute, toleranceReadbackRoute, readbackSealCompletion, provenancePkg,
      completionPkg⟩

end BEDC.Derived.SeparableMetricUp
