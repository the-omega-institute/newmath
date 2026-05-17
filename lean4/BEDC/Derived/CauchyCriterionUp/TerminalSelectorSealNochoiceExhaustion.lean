import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_terminal_selector_seal_nochoice_exhaustion
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN
      selectorRequest selectorSeal pullback terminal noChoiceBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      FiniteObservationBudgetSelectorUp.FiniteObservationBudgetSelectorCarrier
        budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN ->
        Cont endpoint realSeal selectorRequest ->
          Cont selectorRequest budgetE selectorSeal ->
            Cont selectorSeal budgetC pullback ->
              Cont pullback realSeal terminal ->
                Cont terminal localCert noChoiceBoundary ->
                  PkgSig bundle pullback pkg ->
                    PkgSig bundle terminal pkg ->
                      PkgSig bundle noChoiceBoundary pkg ->
                        UnaryHistory selectorRequest ∧ UnaryHistory selectorSeal ∧
                          UnaryHistory pullback ∧ UnaryHistory terminal ∧
                            UnaryHistory noChoiceBoundary ∧
                              Cont endpoint realSeal selectorRequest ∧
                                Cont selectorRequest budgetE selectorSeal ∧
                                  Cont selectorSeal budgetC pullback ∧
                                    Cont pullback realSeal terminal ∧
                                      Cont terminal localCert noChoiceBoundary ∧
                                        PkgSig bundle terminal pkg ∧
                                          PkgSig bundle noChoiceBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier budget endpointRealSelector selectorBudgetSeal sealBudgetPullback
    pullbackRealTerminal terminalLocalNoChoice _pullbackPkg terminalPkg noChoicePkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, _endpointPkg⟩ := carrier
  obtain ⟨budgetBUnary, budgetSUnary, budgetDUnary, budgetEUnary, _budgetHUnary,
    budgetRouteW, budgetRouteR, budgetRouteC, _sameBudgetName⟩ := budget
  have budgetWUnary : UnaryHistory budgetW :=
    unary_cont_closed budgetBUnary budgetSUnary budgetRouteW
  have budgetRUnary : UnaryHistory budgetR :=
    unary_cont_closed budgetWUnary budgetDUnary budgetRouteR
  have budgetCUnary : UnaryHistory budgetC :=
    unary_cont_closed budgetRUnary budgetEUnary budgetRouteC
  have selectorRequestUnary : UnaryHistory selectorRequest :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSelector
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed selectorRequestUnary budgetEUnary selectorBudgetSeal
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed selectorSealUnary budgetCUnary sealBudgetPullback
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed pullbackUnary realSealUnary pullbackRealTerminal
  have noChoiceUnary : UnaryHistory noChoiceBoundary :=
    unary_cont_closed terminalUnary localCertUnary terminalLocalNoChoice
  exact
    ⟨selectorRequestUnary, selectorSealUnary, pullbackUnary, terminalUnary, noChoiceUnary,
      endpointRealSelector, selectorBudgetSeal, sealBudgetPullback, pullbackRealTerminal,
      terminalLocalNoChoice, terminalPkg, noChoicePkg⟩

end BEDC.Derived.CauchyCriterionUp
