import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityTerminalSelectorNonescape [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector sealBudget terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector sealRow sealBudget ->
          Cont readback realSeal terminal ->
            PkgSig bundle terminal pkg ->
              UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                UnaryHistory windows ∧ UnaryHistory selector ∧ UnaryHistory sealBudget ∧
                  UnaryHistory terminal ∧ Cont diagonal windows selector ∧
                    Cont selector sealRow sealBudget ∧ Cont readback realSeal terminal ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro carrier diagonalWindowsSelector selectorSealBudget readbackRealSealTerminal terminalPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed selectorUnary sealRowUnary selectorSealBudget
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, selectorUnary,
      sealBudgetUnary, terminalUnary, diagonalWindowsSelector, selectorSealBudget,
      readbackRealSealTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
