import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_seal_boundary [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootBudget rootWindow rootSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic rootBudget →
        Cont rootBudget windows rootWindow →
          Cont rootWindow realSeal rootSeal →
            PkgSig bundle rootSeal pkg →
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory realSeal ∧ UnaryHistory rootBudget ∧ UnaryHistory rootWindow ∧
                  UnaryHistory rootSeal ∧ Cont diagonal dyadic rootBudget ∧
                    Cont rootBudget windows rootWindow ∧ Cont rootWindow realSeal rootSeal ∧
                      Cont dyadic windows readback ∧ Cont readback realSeal route ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle rootSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalDyadicRoot rootWindowsRootWindow rootWindowRealSealRoot rootSealPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootBudgetUnary : UnaryHistory rootBudget :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRoot
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed rootBudgetUnary windowsUnary rootWindowsRootWindow
  have rootSealUnary : UnaryHistory rootSeal :=
    unary_cont_closed rootWindowUnary realSealUnary rootWindowRealSealRoot
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, realSealUnary, rootBudgetUnary,
      rootWindowUnary, rootSealUnary, diagonalDyadicRoot, rootWindowsRootWindow,
      rootWindowRealSealRoot, dyadicWindowsReadback, readbackRealSealRoute, provenancePkg,
      rootSealPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
