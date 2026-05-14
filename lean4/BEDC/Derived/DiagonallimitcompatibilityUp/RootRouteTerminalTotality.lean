import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteTerminalTotality [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert budgetRoot budgetWindow budgetRead budgetSeal terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetRoot ->
        Cont budgetRoot windows budgetWindow ->
          Cont budgetWindow readback budgetRead ->
            Cont budgetRead realSeal budgetSeal ->
              Cont budgetSeal route terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory budgetRoot ∧ UnaryHistory budgetWindow ∧
                    UnaryHistory budgetRead ∧ UnaryHistory budgetSeal ∧
                      UnaryHistory terminal ∧ Cont diagonal dyadic budgetRoot ∧
                        Cont budgetRoot windows budgetWindow ∧
                          Cont budgetWindow readback budgetRead ∧
                            Cont budgetRead realSeal budgetSeal ∧
                              Cont budgetSeal route terminal ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicBudgetRoot budgetRootWindowsBudgetWindow
    budgetWindowReadbackBudgetRead budgetReadRealSealBudgetSeal budgetSealRouteTerminal
    terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetRoot
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary budgetRootWindowsBudgetWindow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowReadbackBudgetRead
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetReadUnary realSealUnary budgetReadRealSealBudgetSeal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed budgetSealUnary routeUnary budgetSealRouteTerminal
  exact
    ⟨budgetRootUnary, budgetWindowUnary, budgetReadUnary, budgetSealUnary, terminalUnary,
      diagonalDyadicBudgetRoot, budgetRootWindowsBudgetWindow, budgetWindowReadbackBudgetRead,
      budgetReadRealSealBudgetSeal, budgetSealRouteTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
