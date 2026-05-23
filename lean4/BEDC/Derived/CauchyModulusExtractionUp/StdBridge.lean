import BEDC.Derived.CauchyModulusExtractionUp

namespace BEDC.Derived.CauchyModulusExtractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusExtractionUp_StdBridge [AskSetup] [PackageSetup]
    {tolerance budget windows schedule modulus dyadic transport route provenance cert
      consumer bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusExtractionCarrier tolerance budget windows schedule modulus dyadic transport
        route provenance cert bundle pkg ->
      Cont schedule dyadic consumer ->
        Cont consumer provenance bridgeRead ->
          PkgSig bundle consumer pkg ->
            PkgSig bundle bridgeRead pkg ->
              UnaryHistory bridgeRead ∧ Cont schedule dyadic consumer ∧
                Cont consumer provenance bridgeRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg ∧ PkgSig bundle bridgeRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                      (fun row : BHist => hsame row provenance)
                      (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier scheduleDyadicConsumer consumerProvenanceBridge consumerPkg bridgePkg
  obtain ⟨_toleranceUnary, _budgetUnary, _windowsUnary, _scheduleUnary, _modulusUnary,
    _dyadicUnary, _consumerUnary, _toleranceBudgetWindows, _windowsScheduleModulus,
    _scheduleDyadicConsumer, provenancePkg, _consumerPkg, cert⟩ :=
    CauchyModulusExtractionCarrier_namecert_obligations carrier scheduleDyadicConsumer
      consumerPkg
  obtain ⟨_toleranceUnary', _budgetUnary', _windowsUnary', _scheduleUnary',
    _modulusUnary', _dyadicUnary', _transportUnary', _routeUnary', provenanceUnary,
    _certUnary', _toleranceBudgetWindows', _windowsScheduleModulus',
    _modulusDyadicTransport', _transportRouteProvenance', _provenancePkg'⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed _scheduleUnary _dyadicUnary scheduleDyadicConsumer
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed consumerUnary provenanceUnary consumerProvenanceBridge
  exact
    ⟨bridgeUnary, scheduleDyadicConsumer, consumerProvenanceBridge, provenancePkg,
      consumerPkg, bridgePkg, cert⟩

end BEDC.Derived.CauchyModulusExtractionUp
