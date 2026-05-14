import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_window_route [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRoot budgetWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetRoot ->
      Cont budgetRoot windows budgetWindow ->
      PkgSig bundle budgetWindow pkg ->
        UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
          UnaryHistory budgetRoot ∧ UnaryHistory budgetWindow ∧
            Cont diagonal dyadic budgetRoot ∧ Cont budgetRoot windows budgetWindow ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle budgetWindow pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier diagonalDyadicBudgetRoot budgetRootWindowsBudgetWindow budgetWindowPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetRoot
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary budgetRootWindowsBudgetWindow
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, budgetRootUnary, budgetWindowUnary,
      diagonalDyadicBudgetRoot, budgetRootWindowsBudgetWindow, provenancePkg, budgetWindowPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
