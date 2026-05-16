import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_selector_budget_common_refinement
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector regularBudget modulusRefinement sealConsumer commonTerminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector dyadic regularBudget ->
          Cont selector readback modulusRefinement ->
            Cont modulusRefinement realSeal sealConsumer ->
              Cont regularBudget sealConsumer commonTerminal ->
                PkgSig bundle commonTerminal pkg ->
                  UnaryHistory selector ∧ UnaryHistory regularBudget ∧
                    UnaryHistory modulusRefinement ∧ UnaryHistory sealConsumer ∧
                      UnaryHistory commonTerminal ∧ Cont diagonal windows selector ∧
                        Cont selector dyadic regularBudget ∧
                          Cont selector readback modulusRefinement ∧
                            Cont modulusRefinement realSeal sealConsumer ∧
                              Cont regularBudget sealConsumer commonTerminal ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle commonTerminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier diagonalWindowsSelector selectorDyadicRegular selectorReadbackRefinement
    refinementRealSealConsumer regularConsumerTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have regularBudgetUnary : UnaryHistory regularBudget :=
    unary_cont_closed selectorUnary dyadicUnary selectorDyadicRegular
  have modulusRefinementUnary : UnaryHistory modulusRefinement :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackRefinement
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed modulusRefinementUnary realSealUnary refinementRealSealConsumer
  have commonTerminalUnary : UnaryHistory commonTerminal :=
    unary_cont_closed regularBudgetUnary sealConsumerUnary regularConsumerTerminal
  exact
    ⟨selectorUnary, regularBudgetUnary, modulusRefinementUnary, sealConsumerUnary,
      commonTerminalUnary, diagonalWindowsSelector, selectorDyadicRegular,
      selectorReadbackRefinement, refinementRealSealConsumer, regularConsumerTerminal,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
