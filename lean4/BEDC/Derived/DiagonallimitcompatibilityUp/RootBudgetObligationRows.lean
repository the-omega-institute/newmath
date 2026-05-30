import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_budget_classifier_row [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      diagonal' dyadic' windows' readback' realSeal' budgetRoot budgetWindow budgetRead
      budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      hsame diagonal diagonal' ->
        hsame dyadic dyadic' ->
          hsame windows windows' ->
            hsame readback readback' ->
              hsame realSeal realSeal' ->
                Cont diagonal' dyadic' budgetRoot ->
                  Cont budgetRoot windows' budgetWindow ->
                    Cont budgetWindow readback' budgetRead ->
                      Cont budgetRead realSeal' budgetSeal ->
                        PkgSig bundle budgetSeal pkg ->
                          UnaryHistory diagonal' ∧ UnaryHistory dyadic' ∧
                            UnaryHistory windows' ∧ UnaryHistory readback' ∧
                              UnaryHistory realSeal' ∧ UnaryHistory budgetRoot ∧
                                UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                                  UnaryHistory budgetSeal ∧
                                    Cont diagonal' dyadic' budgetRoot ∧
                                      Cont budgetRoot windows' budgetWindow ∧
                                        Cont budgetWindow readback' budgetRead ∧
                                          Cont budgetRead realSeal' budgetSeal ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig
  intro carrier sameDiagonal sameDyadic sameWindows sameReadback sameRealSeal
    diagonalDyadicBudgetRoot budgetRootWindowsBudgetWindow budgetWindowReadbackBudgetRead
    budgetReadRealSealBudgetSeal budgetSealPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_transport diagonalUnary sameDiagonal
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have windowsUnary' : UnaryHistory windows' :=
    unary_transport windowsUnary sameWindows
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary sameRealSeal
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary' dyadicUnary' diagonalDyadicBudgetRoot
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary' budgetRootWindowsBudgetWindow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary' budgetWindowReadbackBudgetRead
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetReadUnary realSealUnary' budgetReadRealSealBudgetSeal
  exact
    ⟨diagonalUnary', dyadicUnary', windowsUnary', readbackUnary', realSealUnary',
      budgetRootUnary, budgetWindowUnary, budgetReadUnary, budgetSealUnary,
      diagonalDyadicBudgetRoot, budgetRootWindowsBudgetWindow,
      budgetWindowReadbackBudgetRead, budgetReadRealSealBudgetSeal, provenancePkg,
      budgetSealPkg⟩

theorem DiagonalLimitCompatibilityRootBudget_ledger_row [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRoot budgetWindow budgetRead budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetRoot ->
        Cont budgetRoot windows budgetWindow ->
          Cont budgetWindow readback budgetRead ->
            Cont budgetRead realSeal budgetSeal ->
              PkgSig bundle budgetSeal pkg ->
                UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
                  UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                    UnaryHistory realSeal ∧ UnaryHistory route ∧ UnaryHistory transport ∧
                      UnaryHistory budgetRoot ∧ UnaryHistory budgetWindow ∧
                        UnaryHistory budgetRead ∧ UnaryHistory budgetSeal ∧
                          Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                            Cont readback realSeal route ∧ Cont route cert transport ∧
                              Cont diagonal dyadic budgetRoot ∧
                                Cont budgetRoot windows budgetWindow ∧
                                  Cont budgetWindow readback budgetRead ∧
                                    Cont budgetRead realSeal budgetSeal ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalDyadicBudgetRoot budgetRootWindowsBudgetWindow
    budgetWindowReadbackBudgetRead budgetReadRealSealBudgetSeal budgetSealPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, transportUnary, routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSealRow, dyadicWindowsReadback, readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetRoot
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary budgetRootWindowsBudgetWindow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowReadbackBudgetRead
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetReadUnary realSealUnary budgetReadRealSealBudgetSeal
  exact
    ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, routeUnary, transportUnary, budgetRootUnary, budgetWindowUnary,
      budgetReadUnary, budgetSealUnary, diagonalTriangleSealRow, dyadicWindowsReadback,
      readbackRealSealRoute, routeCertTransport, diagonalDyadicBudgetRoot,
      budgetRootWindowsBudgetWindow, budgetWindowReadbackBudgetRead,
      budgetReadRealSealBudgetSeal, provenancePkg, budgetSealPkg⟩

theorem DiagonalLimitCompatibilityRootBudget_terminal_route_uniqueness
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      terminal0 terminal1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont readback realSeal terminal0 →
        Cont readback realSeal terminal1 →
          PkgSig bundle terminal0 pkg →
            PkgSig bundle terminal1 pkg →
              hsame terminal0 terminal1 ∧ UnaryHistory terminal0 ∧
                UnaryHistory terminal1 ∧ PkgSig bundle terminal0 pkg ∧
                  PkgSig bundle terminal1 pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig
  intro carrier readbackRealSealTerminal0 readbackRealSealTerminal1 terminal0Pkg
    terminal1Pkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have sameTerminal : hsame terminal0 terminal1 :=
    cont_deterministic readbackRealSealTerminal0 readbackRealSealTerminal1
  have terminal0Unary : UnaryHistory terminal0 :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal0
  have terminal1Unary : UnaryHistory terminal1 :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal1
  exact ⟨sameTerminal, terminal0Unary, terminal1Unary, terminal0Pkg, terminal1Pkg⟩

theorem DiagonalLimitCompatibility_root_budget_selector_synchronizer_exactness
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked sync completion0 completion1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          Cont locked realSeal sync ->
            Cont sync cert completion0 ->
              Cont sync cert completion1 ->
                PkgSig bundle completion0 pkg ->
                  PkgSig bundle completion1 pkg ->
                    hsame completion0 completion1 ∧ UnaryHistory selector ∧
                      UnaryHistory locked ∧ UnaryHistory sync ∧ UnaryHistory completion0 ∧
                        UnaryHistory completion1 ∧ PkgSig bundle completion0 pkg ∧
                          PkgSig bundle completion1 pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealSync
    syncCertCompletion0 syncCertCompletion1 completion0Pkg completion1Pkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have syncUnary : UnaryHistory sync :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealSync
  have completion0Unary : UnaryHistory completion0 :=
    unary_cont_closed syncUnary certUnary syncCertCompletion0
  have completion1Unary : UnaryHistory completion1 :=
    unary_cont_closed syncUnary certUnary syncCertCompletion1
  have sameCompletions : hsame completion0 completion1 :=
    cont_deterministic syncCertCompletion0 syncCertCompletion1
  exact
    ⟨sameCompletions, selectorUnary, lockedUnary, syncUnary, completion0Unary,
      completion1Unary, completion0Pkg, completion1Pkg⟩

theorem DiagonalLimitCompatibilityRootBudgetSelectorSynchronizerExactness
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector synchronizer exact : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic selector ->
        Cont selector windows synchronizer ->
          Cont synchronizer readback exact ->
            PkgSig bundle exact pkg ->
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory readback ∧ UnaryHistory selector ∧ UnaryHistory synchronizer ∧
                  UnaryHistory exact ∧ Cont diagonal dyadic selector ∧
                    Cont selector windows synchronizer ∧ Cont synchronizer readback exact ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle exact pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicSelector selectorWindowsSynchronizer
    synchronizerReadbackExact exactPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSelector
  have synchronizerUnary : UnaryHistory synchronizer :=
    unary_cont_closed selectorUnary windowsUnary selectorWindowsSynchronizer
  have exactUnary : UnaryHistory exact :=
    unary_cont_closed synchronizerUnary readbackUnary synchronizerReadbackExact
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, selectorUnary,
      synchronizerUnary, exactUnary, diagonalDyadicSelector, selectorWindowsSynchronizer,
      synchronizerReadbackExact, provenancePkg, exactPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
