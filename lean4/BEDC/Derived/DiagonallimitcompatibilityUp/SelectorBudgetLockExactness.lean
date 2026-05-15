import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySelectorBudgetLockExactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked budgetPrefix sealBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector readback locked →
          Cont dyadic windows budgetPrefix →
            Cont budgetPrefix sealRow sealBudget →
              PkgSig bundle locked pkg →
                PkgSig bundle sealBudget pkg →
                  UnaryHistory selector ∧ UnaryHistory locked ∧
                    UnaryHistory budgetPrefix ∧ UnaryHistory sealBudget ∧
                      Cont diagonal windows selector ∧ Cont selector readback locked ∧
                        Cont dyadic windows budgetPrefix ∧
                          Cont budgetPrefix sealRow sealBudget ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle locked pkg ∧
                              PkgSig bundle sealBudget pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalWindowsSelector selectorReadbackLocked dyadicWindowsBudgetPrefix
    budgetPrefixSealBudget lockedPkg sealBudgetPkg
  obtain ⟨diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSealRow, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealRowUnary budgetPrefixSealBudget
  exact
    ⟨selectorUnary, lockedUnary, budgetPrefixUnary, sealBudgetUnary,
      diagonalWindowsSelector, selectorReadbackLocked, dyadicWindowsBudgetPrefix,
      budgetPrefixSealBudget, provenancePkg, lockedPkg, sealBudgetPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
