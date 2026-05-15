import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootBudgetSealFactorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRoot budgetWindow budgetRead budgetSeal terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetRoot ->
        Cont budgetRoot windows budgetWindow ->
          Cont budgetWindow readback budgetRead ->
            Cont budgetRead realSeal budgetSeal ->
              Cont route cert terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory budgetRoot ∧ UnaryHistory budgetWindow ∧
                    UnaryHistory budgetRead ∧ UnaryHistory budgetSeal ∧
                      UnaryHistory terminal ∧ Cont diagonal dyadic budgetRoot ∧
                        Cont budgetRoot windows budgetWindow ∧
                          Cont budgetWindow readback budgetRead ∧
                            Cont budgetRead realSeal budgetSeal ∧ Cont route cert terminal ∧
                              hsame transport terminal ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicBudget budgetWindowsRoute budgetReadbackRoute
    budgetRealSealRoute routeCertTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, transportUnary, routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudget
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary budgetWindowsRoute
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetReadbackRoute
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetReadUnary realSealUnary budgetRealSealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed routeUnary certUnary routeCertTerminal
  have sameTerminal : hsame transport terminal :=
    cont_respects_hsame (hsame_refl route) (hsame_refl cert) routeCertTransport
      routeCertTerminal
  exact
    ⟨budgetRootUnary, budgetWindowUnary, budgetReadUnary, budgetSealUnary, terminalUnary,
      diagonalDyadicBudget, budgetWindowsRoute, budgetReadbackRoute, budgetRealSealRoute,
      routeCertTerminal, sameTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
