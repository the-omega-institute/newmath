import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_finite_observation_budget_selector_pullback
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      selectorRequest selectorSeal budgetB budgetS budgetW budgetD budgetR budgetE budgetH
      budgetC budgetP budgetN pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.FiniteObservationBudgetSelectorUp.FiniteObservationBudgetSelectorCarrier
        budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN ->
        Cont endpoint realSeal selectorRequest ->
          Cont selectorRequest budgetE selectorSeal ->
            Cont selectorSeal budgetC pullback ->
              PkgSig bundle pullback pkg ->
                hsame budgetN budgetE ->
                  UnaryHistory selectorRequest ∧ UnaryHistory selectorSeal ∧
                    UnaryHistory pullback ∧ UnaryHistory budgetE ∧
                      Cont endpoint realSeal selectorRequest ∧
                        Cont selectorRequest budgetE selectorSeal ∧
                          Cont selectorSeal budgetC pullback ∧
                            PkgSig bundle endpoint pkg ∧ PkgSig bundle pullback pkg ∧
                              hsame budgetN budgetE := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier budgetCarrier endpointRealSelector selectorBudgetSeal selectorBudgetPullback
    pullbackPkg _sameBudgetName
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  obtain ⟨budgetBUnary, budgetSUnary, budgetDUnary, budgetEUnary, _budgetHUnary,
    budgetSchedule, budgetWindowDyadic, budgetRegularSeal, sameBudgetName⟩ :=
    budgetCarrier
  have budgetWUnary : UnaryHistory budgetW :=
    unary_cont_closed budgetBUnary budgetSUnary budgetSchedule
  have budgetRUnary : UnaryHistory budgetR :=
    unary_cont_closed budgetWUnary budgetDUnary budgetWindowDyadic
  have budgetCUnary : UnaryHistory budgetC :=
    unary_cont_closed budgetRUnary budgetEUnary budgetRegularSeal
  have selectorRequestUnary : UnaryHistory selectorRequest :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSelector
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed selectorRequestUnary budgetEUnary selectorBudgetSeal
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed selectorSealUnary budgetCUnary selectorBudgetPullback
  exact
    ⟨selectorRequestUnary, selectorSealUnary, pullbackUnary, budgetEUnary,
      endpointRealSelector, selectorBudgetSeal, selectorBudgetPullback, endpointPkg, pullbackPkg,
      sameBudgetName⟩

end BEDC.Derived.CauchyCriterionUp
