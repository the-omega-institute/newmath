import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteTerminalBudgetLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert budgetSource windowLock regularRead sealRoute terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetSource ->
        Cont budgetSource windows windowLock ->
          Cont windowLock readback regularRead ->
            Cont regularRead sealRow sealRoute ->
              Cont sealRoute realSeal terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory realSeal ∧
                      UnaryHistory budgetSource ∧ UnaryHistory windowLock ∧
                        UnaryHistory regularRead ∧ UnaryHistory sealRoute ∧
                          UnaryHistory terminal ∧ Cont diagonal dyadic budgetSource ∧
                            Cont budgetSource windows windowLock ∧
                              Cont windowLock readback regularRead ∧
                                Cont regularRead sealRow sealRoute ∧
                                  Cont sealRoute realSeal terminal ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicBudgetSource budgetSourceWindowsWindowLock
    windowLockReadbackRegularRead regularReadSealRowSealRoute sealRouteRealSealTerminal
    terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetSourceUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetSource
  have windowLockUnary : UnaryHistory windowLock :=
    unary_cont_closed budgetSourceUnary windowsUnary budgetSourceWindowsWindowLock
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed windowLockUnary readbackUnary windowLockReadbackRegularRead
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed regularReadUnary sealRowUnary regularReadSealRowSealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealRouteUnary realSealUnary sealRouteRealSealTerminal
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, sealRowUnary,
      realSealUnary, budgetSourceUnary, windowLockUnary, regularReadUnary,
      sealRouteUnary, terminalUnary, diagonalDyadicBudgetSource,
      budgetSourceWindowsWindowLock, windowLockReadbackRegularRead,
      regularReadSealRowSealRoute, sealRouteRealSealTerminal, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
