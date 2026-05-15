import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_root_budget_handoff_totality [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRoot selectorRead sealRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic budgetRoot →
        Cont budgetRoot windows selectorRead →
          Cont selectorRead readback sealRead →
            Cont sealRead realSeal terminal →
              PkgSig bundle terminal pkg →
                UnaryHistory budgetRoot ∧ UnaryHistory selectorRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory terminal ∧
                    Cont diagonal dyadic budgetRoot ∧ Cont budgetRoot windows selectorRead ∧
                      Cont selectorRead readback sealRead ∧ Cont sealRead realSeal terminal ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalDyadicBudgetRoot budgetRootWindowsSelectorRead
    selectorReadReadbackSealRead sealReadRealSealTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSealRow, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetRoot
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed budgetRootUnary windowsUnary budgetRootWindowsSelectorRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectorReadUnary readbackUnary selectorReadReadbackSealRead
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealReadUnary realSealUnary sealReadRealSealTerminal
  exact
    ⟨budgetRootUnary, selectorReadUnary, sealReadUnary, terminalUnary,
      diagonalDyadicBudgetRoot, budgetRootWindowsSelectorRead, selectorReadReadbackSealRead,
      sealReadRealSealTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
