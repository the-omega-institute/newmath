import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_finite_observation_budget_factorization
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector synchronizer request budget terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector dyadic synchronizer ->
          Cont synchronizer readback request ->
            Cont request realSeal budget ->
              Cont budget cert terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory selector ∧ UnaryHistory synchronizer ∧ UnaryHistory request ∧
                    UnaryHistory budget ∧ UnaryHistory terminal ∧
                      Cont diagonal windows selector ∧ Cont selector dyadic synchronizer ∧
                        Cont synchronizer readback request ∧ Cont request realSeal budget ∧
                          Cont budget cert terminal ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalWindowsSelector selectorDyadicSynchronizer
    synchronizerReadbackRequest requestRealSealBudget budgetCertTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have synchronizerUnary : UnaryHistory synchronizer :=
    unary_cont_closed selectorUnary dyadicUnary selectorDyadicSynchronizer
  have requestUnary : UnaryHistory request :=
    unary_cont_closed synchronizerUnary readbackUnary synchronizerReadbackRequest
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed requestUnary realSealUnary requestRealSealBudget
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed budgetUnary certUnary budgetCertTerminal
  exact
    ⟨selectorUnary, synchronizerUnary, requestUnary, budgetUnary, terminalUnary,
      diagonalWindowsSelector, selectorDyadicSynchronizer, synchronizerReadbackRequest,
      requestRealSealBudget, budgetCertTerminal, provenancePkg, terminalPkg⟩

theorem DiagonalLimitCompatibility_finite_observation_budget_factorization [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector request sealBudget tail sync locked endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UnaryHistory request →
        UnaryHistory tail →
          Cont diagonal windows selector →
            Cont selector request sealBudget →
              Cont sealBudget tail sync →
                Cont sync readback locked →
                  Cont locked realSeal endpoint →
                    PkgSig bundle locked pkg →
                      PkgSig bundle endpoint pkg →
                        UnaryHistory diagonal ∧ UnaryHistory windows ∧
                          UnaryHistory selector ∧ UnaryHistory request ∧
                            UnaryHistory sealBudget ∧ UnaryHistory tail ∧
                              UnaryHistory sync ∧ UnaryHistory readback ∧
                                UnaryHistory locked ∧ UnaryHistory realSeal ∧
                                  UnaryHistory endpoint ∧ Cont diagonal windows selector ∧
                                    Cont selector request sealBudget ∧
                                      Cont sealBudget tail sync ∧
                                        Cont sync readback locked ∧
                                          Cont locked realSeal endpoint ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle locked pkg ∧
                                                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro carrier requestUnary tailUnary diagonalWindowsSelector selectorRequestSealBudget
    sealBudgetTailSync syncReadbackLocked lockedRealSealEndpoint lockedPkg endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed selectorUnary requestUnary selectorRequestSealBudget
  have syncUnary : UnaryHistory sync :=
    unary_cont_closed sealBudgetUnary tailUnary sealBudgetTailSync
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed syncUnary readbackUnary syncReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact
    ⟨diagonalUnary, windowsUnary, selectorUnary, requestUnary, sealBudgetUnary, tailUnary,
      syncUnary, readbackUnary, lockedUnary, realSealUnary, endpointUnary,
      diagonalWindowsSelector, selectorRequestSealBudget, sealBudgetTailSync,
      syncReadbackLocked, lockedRealSealEndpoint, provenancePkg, lockedPkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
