import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootBudgetConsumerChain [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRoot budgetWindow budgetRead budgetSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetRoot ->
        Cont budgetRoot windows budgetWindow ->
          Cont budgetWindow readback budgetRead ->
            Cont budgetRead realSeal budgetSeal ->
              Cont budgetSeal route publicRead ->
                PkgSig bundle publicRead pkg ->
                  UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory route ∧
                      UnaryHistory budgetRoot ∧ UnaryHistory budgetWindow ∧
                        UnaryHistory budgetRead ∧ UnaryHistory budgetSeal ∧
                          UnaryHistory publicRead ∧ Cont diagonal dyadic budgetRoot ∧
                            Cont budgetRoot windows budgetWindow ∧
                              Cont budgetWindow readback budgetRead ∧
                                Cont budgetRead realSeal budgetSeal ∧
                                  Cont budgetSeal route publicRead ∧
                                    Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalDyadicBudgetRoot budgetRootWindowsBudgetWindow
    budgetWindowReadbackBudgetRead budgetReadRealSealBudgetSeal budgetSealRoutePublicRead
    publicReadPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute, routeCertTransport,
    provenancePkg⟩ := carrier
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetRoot
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary budgetRootWindowsBudgetWindow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowReadbackBudgetRead
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetReadUnary realSealUnary budgetReadRealSealBudgetSeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed budgetSealUnary routeUnary budgetSealRoutePublicRead
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary, routeUnary,
      budgetRootUnary, budgetWindowUnary, budgetReadUnary, budgetSealUnary, publicReadUnary,
      diagonalDyadicBudgetRoot, budgetRootWindowsBudgetWindow, budgetWindowReadbackBudgetRead,
      budgetReadRealSealBudgetSeal, budgetSealRoutePublicRead, routeCertTransport,
      provenancePkg, publicReadPkg⟩

theorem DiagonalLimitCompatibility_budget_coherence_terminal_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootBudget rootWindow rootReadback rootSeal terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic rootBudget ->
        Cont rootBudget windows rootWindow ->
          Cont rootWindow readback rootReadback ->
            Cont rootReadback realSeal rootSeal ->
              Cont rootSeal cert terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory cert ∧
                      UnaryHistory rootBudget ∧ UnaryHistory rootWindow ∧
                        UnaryHistory rootReadback ∧ UnaryHistory rootSeal ∧
                          UnaryHistory terminal ∧ Cont diagonal dyadic rootBudget ∧
                            Cont rootBudget windows rootWindow ∧
                              Cont rootWindow readback rootReadback ∧
                                Cont rootReadback realSeal rootSeal ∧
                                  Cont rootSeal cert terminal ∧ Cont route cert transport ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier diagonalDyadicRootBudget rootBudgetWindowsRootWindow
    rootWindowReadbackRootReadback rootReadbackRealSealRootSeal rootSealCertTerminal
    terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have rootBudgetUnary : UnaryHistory rootBudget :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRootBudget
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed rootBudgetUnary windowsUnary rootBudgetWindowsRootWindow
  have rootReadbackUnary : UnaryHistory rootReadback :=
    unary_cont_closed rootWindowUnary readbackUnary rootWindowReadbackRootReadback
  have rootSealUnary : UnaryHistory rootSeal :=
    unary_cont_closed rootReadbackUnary realSealUnary rootReadbackRealSealRootSeal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed rootSealUnary certUnary rootSealCertTerminal
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary, certUnary,
      rootBudgetUnary, rootWindowUnary, rootReadbackUnary, rootSealUnary, terminalUnary,
      diagonalDyadicRootBudget, rootBudgetWindowsRootWindow, rootWindowReadbackRootReadback,
      rootReadbackRealSealRootSeal, rootSealCertTerminal, routeCertTransport,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
