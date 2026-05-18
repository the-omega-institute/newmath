import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_finite_observation_budget_selector_uniqueness
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP
      budgetN budgetW' budgetR' budgetC' selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.FiniteObservationBudgetSelectorUp.FiniteObservationBudgetSelectorCarrier
        budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN ->
        Cont budgetB budgetS budgetW' ->
          Cont budgetW' budgetD budgetR' ->
            Cont budgetR' budgetE budgetC' ->
              Cont endpoint realSeal selectorRead ->
                PkgSig bundle selectorRead pkg ->
                  hsame budgetW budgetW' ∧ hsame budgetR budgetR' ∧
                    hsame budgetC budgetC' ∧ UnaryHistory selectorRead ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier budgetCarrier budgetSchedule windowDyadic regularSeal endpointRealSelector
    selectorPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  obtain ⟨sameBudgetWindow, sameBudgetRegular, sameBudgetSeal⟩ :=
    BEDC.Derived.FiniteObservationBudgetSelectorUp.FiniteObservationBudgetSelectorCarrier_budget_route_determinacy
      (inferInstance : PackageSetup) budgetCarrier
        budgetSchedule windowDyadic regularSeal
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSelector
  exact
    ⟨sameBudgetWindow, sameBudgetRegular, sameBudgetSeal, selectorUnary, endpointPkg,
      selectorPkg⟩

end BEDC.Derived.CauchyCriterionUp
