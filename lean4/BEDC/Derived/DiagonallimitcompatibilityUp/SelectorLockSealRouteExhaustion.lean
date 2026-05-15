import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySelectorLockSealRouteExhaustion [AskSetup] [PackageSetup]
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
                        UnaryHistory selector ∧ UnaryHistory sealBudget ∧
                          UnaryHistory sync ∧ UnaryHistory locked ∧ UnaryHistory endpoint ∧
                            Cont diagonal windows selector ∧
                              Cont selector request sealBudget ∧ Cont sealBudget tail sync ∧
                                Cont sync readback locked ∧ Cont locked realSeal endpoint ∧
                                  PkgSig bundle provenance pkg ∧ PkgSig bundle locked pkg ∧
                                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier requestUnary tailUnary diagonalWindowsSelector selectorRequestSealBudget
    sealBudgetTailSync syncReadbackLocked lockedRealSealEndpoint lockedPkg endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
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
    ⟨selectorUnary, sealBudgetUnary, syncUnary, lockedUnary, endpointUnary,
      diagonalWindowsSelector, selectorRequestSealBudget, sealBudgetTailSync,
      syncReadbackLocked, lockedRealSealEndpoint, provenancePkg, lockedPkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
