import BEDC.Derived.BaireCategoryUp.CompleteMetricThreadExtraction

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_nested_ball_thread_totality [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead threadRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg ->
      Cont D O R ->
        Cont R T threadRead ->
          Cont threadRead M terminalRead ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory B ∧ UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory O ∧
                UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory threadRead ∧
                  UnaryHistory terminalRead ∧ Cont D O R ∧ Cont R T threadRead ∧
                    Cont threadRead M terminalRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier denseOpenRoute threadRoute terminalRoute terminalPkg
  have extracted :=
    BaireCategoryCarrier_complete_metric_thread_extraction
      (B := B) (M := M) (D := D) (O := O) (R := R) (T := T) (H := H) (C := C)
      (P := P) (N := N) (metricRead := M) (threadRead := threadRead)
      (terminalRead := terminalRead) (bundle := bundle) (pkg := pkg)
      carrier denseOpenRoute threadRoute terminalRoute (hsame_refl M) terminalPkg
  obtain ⟨metricUnary, denseUnary, openUnary, refinementUnary, threadUnary,
    _metricReadUnary, threadReadUnary, terminalReadUnary, denseOpenRouteOut,
    threadRouteOut, terminalRouteOut, _metricSame, provenancePkg, terminalPkgOut⟩ :=
    extracted
  obtain ⟨prefixUnary, _metricCarrierUnary, _denseCarrierUnary, _openCarrierUnary,
    _refinementCarrierUnary, _threadCarrierUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _provenancePkgCarrier⟩ := carrier
  exact
    ⟨prefixUnary, metricUnary, denseUnary, openUnary, refinementUnary, threadUnary,
      threadReadUnary, terminalReadUnary, denseOpenRouteOut, threadRouteOut,
      terminalRouteOut, provenancePkg, terminalPkgOut⟩

end BEDC.Derived.BaireCategoryUp
