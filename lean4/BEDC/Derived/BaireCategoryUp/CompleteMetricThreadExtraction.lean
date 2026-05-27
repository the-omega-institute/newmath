import BEDC.Derived.BaireCategoryUp.NameCertObligations
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_complete_metric_thread_extraction [AskSetup] [PackageSetup]
    {B M D O R T H C P N metricRead threadRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg ->
      Cont D O R ->
        Cont R T threadRead ->
          Cont threadRead M terminalRead ->
            hsame metricRead M ->
              PkgSig bundle terminalRead pkg ->
                UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory R ∧
                  UnaryHistory T ∧ UnaryHistory metricRead ∧ UnaryHistory threadRead ∧
                    UnaryHistory terminalRead ∧ Cont D O R ∧ Cont R T threadRead ∧
                      Cont threadRead M terminalRead ∧ hsame metricRead M ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier denseOpenRoute threadRoute terminalRoute metricSame terminalPkg
  obtain ⟨_prefixUnary, metricUnary, denseUnary, openUnary, refinementUnary, threadUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, provenancePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_transport metricUnary (hsame_symm metricSame)
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementUnary threadUnary threadRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed threadReadUnary metricUnary terminalRoute
  exact
    ⟨metricUnary, denseUnary, openUnary, refinementUnary, threadUnary, metricReadUnary,
      threadReadUnary, terminalReadUnary, denseOpenRoute, threadRoute, terminalRoute,
      metricSame, provenancePkg, terminalPkg⟩

end BEDC.Derived.BaireCategoryUp
