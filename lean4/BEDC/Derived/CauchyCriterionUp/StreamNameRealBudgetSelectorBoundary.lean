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

theorem CauchyCriterionCarrier_streamname_real_budget_selector_boundary
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      selectorOutput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont endpoint realSeal selectorOutput ->
        PkgSig bundle selectorOutput pkg ->
          UnaryHistory window ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
            UnaryHistory selectorOutput ∧ Cont endpoint realSeal selectorOutput ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle selectorOutput pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier endpointRealSealSelector selectorOutputPkg
  rcases carrier with
    ⟨windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, regseqUnary,
      realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
      endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
      _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
      endpointPkg⟩
  have selectorOutputUnary : UnaryHistory selectorOutput :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSealSelector
  exact
    ⟨windowUnary, regseqUnary, realSealUnary, selectorOutputUnary,
      endpointRealSealSelector, endpointPkg, selectorOutputPkg⟩

theorem CauchyCriterionCarrier_streamname_real_budget_selector_terminal_boundary
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN
      selectorRead exactBoundaryRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.FiniteObservationBudgetSelectorUp.FiniteObservationBudgetSelectorCarrier
        budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN ->
        Cont ledger realSeal selectorRead ->
          Cont selectorRead budgetE exactBoundaryRead ->
            Cont exactBoundaryRead realSeal terminalRead ->
              PkgSig bundle selectorRead pkg ->
                PkgSig bundle exactBoundaryRead pkg ->
                  PkgSig bundle terminalRead pkg ->
                    UnaryHistory selectorRead ∧ UnaryHistory exactBoundaryRead ∧
                      UnaryHistory terminalRead ∧ Cont ledger realSeal selectorRead ∧
                        Cont selectorRead budgetE exactBoundaryRead ∧
                          Cont exactBoundaryRead realSeal terminalRead ∧
                            PkgSig bundle endpoint pkg ∧
                              PkgSig bundle selectorRead pkg ∧
                                PkgSig bundle exactBoundaryRead pkg ∧
                                  PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier budgetCarrier ledgerRealSealSelector selectorExactBoundary
    exactBoundaryTerminal selectorPkg exactBoundaryPkg terminalPkg
  rcases carrier with
    ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
      realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
      _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
      _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
      endpointPkg⟩
  rcases budgetCarrier with
    ⟨_budgetBUnary, _budgetSUnary, _budgetDUnary, budgetEUnary, _budgetHUnary,
      _budgetRouteW, _budgetRouteR, _budgetRouteC, _budgetSameName⟩
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealSelector
  have exactBoundaryUnary : UnaryHistory exactBoundaryRead :=
    unary_cont_closed selectorUnary budgetEUnary selectorExactBoundary
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed exactBoundaryUnary realSealUnary exactBoundaryTerminal
  exact
    ⟨selectorUnary, exactBoundaryUnary, terminalUnary, ledgerRealSealSelector,
      selectorExactBoundary, exactBoundaryTerminal, endpointPkg, selectorPkg,
      exactBoundaryPkg, terminalPkg⟩

theorem CauchyCriterionCarrier_budget_selector_section_exactness
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN
      sectionRead selectorSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.FiniteObservationBudgetSelectorUp.FiniteObservationBudgetSelectorCarrier
        budgetB budgetS budgetW budgetD budgetR budgetE budgetH budgetC budgetP budgetN ->
        Cont endpoint budgetW sectionRead ->
          Cont sectionRead budgetE selectorSeal ->
            PkgSig bundle sectionRead pkg ->
              PkgSig bundle selectorSeal pkg ->
                UnaryHistory endpoint ∧ UnaryHistory budgetW ∧ UnaryHistory sectionRead ∧
                  UnaryHistory selectorSeal ∧ Cont endpoint budgetW sectionRead ∧
                    Cont sectionRead budgetE selectorSeal ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle sectionRead pkg ∧ PkgSig bundle selectorSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier budgetCarrier endpointBudgetSection sectionSelectorSeal sectionPkg selectorPkg
  rcases carrier with
    ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
      _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
      endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
      _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
      endpointPkg⟩
  rcases budgetCarrier with
    ⟨budgetBUnary, budgetSUnary, _budgetDUnary, budgetEUnary, _budgetHUnary,
      budgetWindowRoute, _budgetRegularRoute, _budgetSealRoute, _budgetSameName⟩
  have budgetWUnary : UnaryHistory budgetW :=
    unary_cont_closed budgetBUnary budgetSUnary budgetWindowRoute
  have sectionUnary : UnaryHistory sectionRead :=
    unary_cont_closed endpointUnary budgetWUnary endpointBudgetSection
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed sectionUnary budgetEUnary sectionSelectorSeal
  exact
    ⟨endpointUnary, budgetWUnary, sectionUnary, selectorSealUnary,
      endpointBudgetSection, sectionSelectorSeal, endpointPkg, sectionPkg, selectorPkg⟩

end BEDC.Derived.CauchyCriterionUp
