import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_selector_seal_pullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selectorRead budgetRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle selectorRead ->
        Cont selectorRead sealRow budgetRead ->
          Cont budgetRead realSeal terminalRead ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory selectorRead ∧ UnaryHistory budgetRead ∧
                UnaryHistory terminalRead ∧ Cont diagonal triangle selectorRead ∧
                  Cont selectorRead sealRow budgetRead ∧
                    Cont budgetRead realSeal terminalRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro carrier diagonalTriangleSelector selectorSealBudget budgetRealTerminal terminalPkg
  rcases carrier with
    ⟨diagonalUnary, triangleUnary, sealUnary, _dyadicUnary, _windowsUnary, _readbackUnary,
      realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
      _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
      _routeCertTransport, provenancePkg⟩
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleSelector
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed selectorUnary sealUnary selectorSealBudget
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetUnary realSealUnary budgetRealTerminal
  exact
    ⟨selectorUnary, budgetUnary, terminalUnary, diagonalTriangleSelector, selectorSealBudget,
      budgetRealTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
