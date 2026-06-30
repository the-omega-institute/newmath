import BEDC.Derived.SeparableCompletionUp.NameCertObligations

namespace BEDC.Derived.SeparableCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparableCompletionDensityHandoff [AskSetup] [PackageSetup]
    {M D C W T R E H P N denseRead toleranceRead readbackRead sealRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableCompletionCarrier M D C W T R E H P N bundle pkg ->
      Cont D W denseRead ->
        Cont denseRead T toleranceRead ->
          Cont toleranceRead R readbackRead ->
            Cont readbackRead C sealRead ->
              Cont sealRead E terminalRead ->
                PkgSig bundle terminalRead pkg ->
                  UnaryHistory denseRead ∧ UnaryHistory toleranceRead ∧
                    UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory terminalRead ∧ Cont D W denseRead ∧
                        Cont denseRead T toleranceRead ∧ Cont toleranceRead R readbackRead ∧
                          Cont readbackRead C sealRead ∧ Cont sealRead E terminalRead ∧
                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory SeparableCompletionCarrier
  intro carrier denseRoute toleranceRoute readbackRoute sealRoute terminalRoute terminalPkg
  obtain ⟨_metricUnary, denseUnary, completionUnary, windowsUnary, toleranceUnary,
    readbackUnary, sealRowUnary, _transportUnary, _provenanceUnary, _localNameUnary,
    _provenancePkg, _localNamePkg⟩ := carrier
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary windowsUnary denseRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denseReadUnary toleranceUnary toleranceRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceReadUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary completionUnary sealRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed sealReadUnary sealRowUnary terminalRoute
  exact
    ⟨denseReadUnary, toleranceReadUnary, readbackReadUnary, sealReadUnary,
      terminalReadUnary, denseRoute, toleranceRoute, readbackRoute, sealRoute,
      terminalRoute, terminalPkg⟩

end BEDC.Derived.SeparableCompletionUp
