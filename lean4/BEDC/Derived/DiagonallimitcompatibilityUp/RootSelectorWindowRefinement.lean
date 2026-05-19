import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootSelectorWindowRefinement [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector request sealBudget tail sync locked windowSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UnaryHistory request →
        UnaryHistory tail →
          Cont diagonal windows selector →
            Cont selector request sealBudget →
              Cont sealBudget tail sync →
                Cont sync readback locked →
                  Cont locked realSeal windowSeal →
                    PkgSig bundle windowSeal pkg →
                      UnaryHistory selector ∧ UnaryHistory sealBudget ∧ UnaryHistory sync ∧
                        UnaryHistory locked ∧ UnaryHistory windowSeal ∧
                          Cont diagonal windows selector ∧ Cont selector request sealBudget ∧
                            Cont sealBudget tail sync ∧ Cont sync readback locked ∧
                              Cont locked realSeal windowSeal ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle windowSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier requestUnary tailUnary diagonalWindowsSelector selectorRequestSealBudget
    sealBudgetTailSync syncReadbackLocked lockedRealSealWindowSeal windowSealPkg
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
  have windowSealUnary : UnaryHistory windowSeal :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealWindowSeal
  exact
    ⟨selectorUnary, sealBudgetUnary, syncUnary, lockedUnary, windowSealUnary,
      diagonalWindowsSelector, selectorRequestSealBudget, sealBudgetTailSync,
      syncReadbackLocked, lockedRealSealWindowSeal, provenancePkg, windowSealPkg⟩

theorem DiagonalLimitCompatibility_root_selector_window_refinement [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      request tail selector sealBudget sync locked endpoint : BHist}
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
                          UnaryHistory request ∧ UnaryHistory tail ∧
                            UnaryHistory selector ∧ UnaryHistory sealBudget ∧
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
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
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
    ⟨diagonalUnary, windowsUnary, requestUnary, tailUnary, selectorUnary, sealBudgetUnary,
      syncUnary, readbackUnary, lockedUnary, realSealUnary, endpointUnary,
      diagonalWindowsSelector, selectorRequestSealBudget, sealBudgetTailSync,
      syncReadbackLocked, lockedRealSealEndpoint, provenancePkg, lockedPkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
