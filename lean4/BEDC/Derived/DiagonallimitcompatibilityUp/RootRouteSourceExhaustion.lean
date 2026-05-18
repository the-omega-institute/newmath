import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteSourceExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRoot budgetWindow budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic budgetRoot →
        Cont budgetRoot windows budgetWindow →
          Cont budgetWindow readback budgetRead →
            PkgSig bundle budgetRead pkg →
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory readback ∧ UnaryHistory budgetRoot ∧
                  UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                    Cont diagonal dyadic budgetRoot ∧
                      Cont budgetRoot windows budgetWindow ∧
                        Cont budgetWindow readback budgetRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalDyadicBudgetRoot budgetRootWindowsBudgetWindow
    budgetWindowReadbackBudgetRead budgetReadPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetRoot
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary budgetRootWindowsBudgetWindow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowReadbackBudgetRead
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, budgetRootUnary,
      budgetWindowUnary, budgetReadUnary, diagonalDyadicBudgetRoot,
      budgetRootWindowsBudgetWindow, budgetWindowReadbackBudgetRead, provenancePkg,
      budgetReadPkg⟩

theorem DiagonalLimitCompatibilityCarrier_root_route_source_exhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetSource meshSource windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetSource ->
        Cont budgetSource triangle meshSource ->
          Cont meshSource windows windowRead ->
            PkgSig bundle windowRead pkg ->
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory triangle ∧
                UnaryHistory windows ∧ UnaryHistory budgetSource ∧
                  UnaryHistory meshSource ∧ UnaryHistory windowRead ∧
                    Cont diagonal dyadic budgetSource ∧
                      Cont budgetSource triangle meshSource ∧
                        Cont meshSource windows windowRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier diagonalDyadicBudget budgetTriangleMesh meshWindowsRead windowPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudget
  have meshUnary : UnaryHistory meshSource :=
    unary_cont_closed budgetUnary triangleUnary budgetTriangleMesh
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed meshUnary windowsUnary meshWindowsRead
  exact
    ⟨diagonalUnary, dyadicUnary, triangleUnary, windowsUnary, budgetUnary, meshUnary,
      windowUnary, diagonalDyadicBudget, budgetTriangleMesh, meshWindowsRead, provenancePkg,
      windowPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
