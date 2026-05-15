import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_budget_public_boundary
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRoot budgetWindow budgetRead budgetSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic budgetRoot →
        Cont budgetRoot windows budgetWindow →
          Cont budgetWindow readback budgetRead →
            Cont budgetRead realSeal budgetSeal →
              Cont budgetSeal cert publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory budgetRoot ∧ UnaryHistory budgetWindow ∧
                    UnaryHistory budgetRead ∧ UnaryHistory budgetSeal ∧
                      UnaryHistory publicRead ∧ Cont diagonal dyadic budgetRoot ∧
                        Cont budgetRoot windows budgetWindow ∧
                          Cont budgetWindow readback budgetRead ∧
                            Cont budgetRead realSeal budgetSeal ∧
                              Cont budgetSeal cert publicRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalDyadicBudgetRoot budgetRootWindowsBudgetWindow
    budgetWindowReadbackBudgetRead budgetReadRealSealBudgetSeal budgetSealCertPublic publicPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetRoot
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary budgetRootWindowsBudgetWindow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowReadbackBudgetRead
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetReadUnary realSealUnary budgetReadRealSealBudgetSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed budgetSealUnary certUnary budgetSealCertPublic
  exact
    ⟨budgetRootUnary, budgetWindowUnary, budgetReadUnary, budgetSealUnary, publicUnary,
      diagonalDyadicBudgetRoot, budgetRootWindowsBudgetWindow, budgetWindowReadbackBudgetRead,
      budgetReadRealSealBudgetSeal, budgetSealCertPublic, provenancePkg, publicPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
