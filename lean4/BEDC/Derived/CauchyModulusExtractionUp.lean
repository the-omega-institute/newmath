import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusExtractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusExtractionCarrier [AskSetup] [PackageSetup]
    (tolerance budget windows schedule modulus dyadic transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tolerance ∧ UnaryHistory budget ∧ UnaryHistory windows ∧
    UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory cert ∧ Cont tolerance budget windows ∧ Cont windows schedule modulus ∧
          Cont modulus dyadic transport ∧ Cont transport route provenance ∧
            PkgSig bundle provenance pkg

theorem CauchyModulusExtractionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {tolerance budget windows schedule modulus dyadic transport route provenance cert
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusExtractionCarrier tolerance budget windows schedule modulus dyadic transport
        route provenance cert bundle pkg ->
      Cont schedule dyadic consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory tolerance ∧ UnaryHistory budget ∧ UnaryHistory windows ∧
            UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
              UnaryHistory consumer ∧ Cont tolerance budget windows ∧
                Cont windows schedule modulus ∧ Cont schedule dyadic consumer ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                      (fun row : BHist => hsame row provenance)
                      (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle SemanticNameCert
  intro carrier scheduleDyadicConsumer consumerPkg
  obtain ⟨toleranceUnary, budgetUnary, windowsUnary, scheduleUnary, modulusUnary, dyadicUnary,
    _transportUnary, _routeUnary, provenanceUnary, _certUnary, toleranceBudgetWindows,
    windowsScheduleModulus, _modulusDyadicTransport, _transportRouteProvenance,
    provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed scheduleUnary dyadicUnary scheduleDyadicConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, provenanceUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨toleranceUnary, budgetUnary, windowsUnary, scheduleUnary, modulusUnary, dyadicUnary,
      consumerUnary, toleranceBudgetWindows, windowsScheduleModulus, scheduleDyadicConsumer,
      provenancePkg, consumerPkg, cert⟩

theorem CauchyModulusExtractionCarrier_dyadic_ledger_positivity [AskSetup] [PackageSetup]
    {tolerance budget windows schedule modulus dyadic transport route provenance cert
      threshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusExtractionCarrier tolerance budget windows schedule modulus dyadic transport
        route provenance cert bundle pkg ->
      Cont modulus dyadic threshold ->
        PkgSig bundle threshold pkg ->
          UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory transport ∧
            UnaryHistory threshold ∧ hsame transport threshold ∧
              Cont modulus dyadic transport ∧ Cont modulus dyadic threshold ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle threshold pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle hsame UnaryHistory
  intro carrier modulusDyadicThreshold thresholdPkg
  obtain ⟨_toleranceUnary, _budgetUnary, _windowsUnary, _scheduleUnary, modulusUnary,
    dyadicUnary, transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _toleranceBudgetWindows, _windowsScheduleModulus, modulusDyadicTransport,
    _transportRouteProvenance, provenancePkg⟩ := carrier
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed modulusUnary dyadicUnary modulusDyadicThreshold
  have sameTransportThreshold : hsame transport threshold :=
    cont_respects_hsame (hsame_refl modulus) (hsame_refl dyadic) modulusDyadicTransport
      modulusDyadicThreshold
  exact
    ⟨modulusUnary, dyadicUnary, transportUnary, thresholdUnary, sameTransportThreshold,
      modulusDyadicTransport, modulusDyadicThreshold, provenancePkg, thresholdPkg⟩

end BEDC.Derived.CauchyModulusExtractionUp
