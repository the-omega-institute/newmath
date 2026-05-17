import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_selector_budget_three_way_terminality
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN
      selectorRequest selectorSeal pullback terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      FiniteObservationBudgetSelectorUp.FiniteObservationBudgetSelectorCarrier
        budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN ->
        Cont endpoint realSeal selectorRequest ->
          Cont selectorRequest budgetE selectorSeal ->
            Cont selectorSeal budgetC pullback ->
              Cont pullback realSeal terminal ->
                hsame terminal pullback ->
                  PkgSig bundle pullback pkg ->
                    PkgSig bundle terminal pkg ->
                      SemanticNameCert (fun row : BHist => hsame row terminal)
                        (fun row : BHist =>
                          Cont selectorRequest budgetE selectorSeal ∧
                            Cont selectorSeal budgetC pullback ∧ hsame row pullback)
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminal pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier budget endpointRealSelector selectorBudgetSeal sealBudgetPullback
    pullbackRealTerminal terminalPullback _pullbackPkg terminalPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
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
  exact {
    core := {
      carrier_inhabited := Exists.intro terminal (hsame_refl terminal)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact hsame_trans (hsame_symm same) source
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨selectorBudgetSeal, sealBudgetPullback,
          hsame_trans source terminalPullback⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport terminalUnary (hsame_symm source), terminalPkg⟩
  }

end BEDC.Derived.CauchyCriterionUp
