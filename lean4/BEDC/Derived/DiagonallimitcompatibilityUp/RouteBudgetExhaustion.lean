import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_route_budget_exhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      source mesh locked budgetPrefix sealBudget terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic source →
        Cont source windows mesh →
          Cont mesh triangle locked →
            Cont dyadic windows budgetPrefix →
              Cont budgetPrefix sealRow sealBudget →
                Cont sealBudget realSeal terminal →
                  PkgSig bundle locked pkg →
                    PkgSig bundle sealBudget pkg →
                      PkgSig bundle terminal pkg →
                        UnaryHistory source ∧ UnaryHistory mesh ∧ UnaryHistory locked ∧
                          UnaryHistory budgetPrefix ∧ UnaryHistory sealBudget ∧
                            UnaryHistory terminal ∧ Cont diagonal dyadic source ∧
                              Cont source windows mesh ∧ Cont mesh triangle locked ∧
                                Cont dyadic windows budgetPrefix ∧
                                  Cont budgetPrefix sealRow sealBudget ∧
                                    Cont sealBudget realSeal terminal ∧
                                      PkgSig bundle provenance pkg ∧ PkgSig bundle locked pkg ∧
                                        PkgSig bundle sealBudget pkg ∧
                                          PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier diagonalDyadicSource sourceWindowsMesh meshTriangleLocked
    dyadicWindowsBudgetPrefix budgetPrefixSealRowSealBudget sealBudgetRealSealTerminal
    lockedPkg sealBudgetPkg terminalPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSource
  have meshUnary : UnaryHistory mesh :=
    unary_cont_closed sourceUnary windowsUnary sourceWindowsMesh
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed meshUnary triangleUnary meshTriangleLocked
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealRowUnary budgetPrefixSealRowSealBudget
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealBudgetUnary realSealUnary sealBudgetRealSealTerminal
  exact
    ⟨sourceUnary, meshUnary, lockedUnary, budgetPrefixUnary, sealBudgetUnary, terminalUnary,
      diagonalDyadicSource, sourceWindowsMesh, meshTriangleLocked, dyadicWindowsBudgetPrefix,
      budgetPrefixSealRowSealBudget, sealBudgetRealSealTerminal, provenancePkg, lockedPkg,
      sealBudgetPkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
