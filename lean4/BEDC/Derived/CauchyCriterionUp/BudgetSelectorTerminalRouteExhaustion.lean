import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.FiniteObservationBudgetSelectorUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_budget_selector_terminal_route_exhaustion
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      index windowsU modulusU toleranceU tail sealRow transportsU routesU provenanceU nameU
      budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN
      selectorRequest selectorSeal pullback terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.UniformCauchyCriterionUp.UniformCauchyCriterionPacket index windowsU
        modulusU toleranceU tail sealRow transportsU routesU provenanceU nameU bundle pkg ->
        BEDC.Derived.FiniteObservationBudgetSelectorUp.FiniteObservationBudgetSelectorCarrier
          budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN ->
          hsame ledger tail ->
            hsame realSeal sealRow ->
              Cont endpoint realSeal selectorRequest ->
                Cont selectorRequest budgetE selectorSeal ->
                  Cont selectorSeal budgetC pullback ->
                    Cont pullback realSeal terminal ->
                      PkgSig bundle pullback pkg ->
                        PkgSig bundle terminal pkg ->
                          UnaryHistory endpoint ∧ UnaryHistory selectorRequest ∧
                            UnaryHistory selectorSeal ∧ UnaryHistory pullback ∧
                              UnaryHistory terminal ∧ Cont endpoint realSeal selectorRequest ∧
                                Cont selectorRequest budgetE selectorSeal ∧
                                  Cont selectorSeal budgetC pullback ∧
                                    Cont pullback realSeal terminal ∧
                                      PkgSig bundle endpoint pkg ∧
                                        PkgSig bundle pullback pkg ∧
                                          PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier _uniform budget _sameLedgerTail _sameRealSealSealRow endpointRealSelector
    selectorBudgetSeal sealBudgetPullback pullbackRealTerminal pullbackPkg terminalPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
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
  exact
    ⟨endpointUnary, selectorRequestUnary, selectorSealUnary, pullbackUnary, terminalUnary,
      endpointRealSelector, selectorBudgetSeal, sealBudgetPullback, pullbackRealTerminal,
      endpointPkg, pullbackPkg, terminalPkg⟩

end BEDC.Derived.CauchyCriterionUp
