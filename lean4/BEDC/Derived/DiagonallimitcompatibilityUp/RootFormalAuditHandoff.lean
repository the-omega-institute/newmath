import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootFormalAuditHandoff [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootBudget rootWindow rootReadback rootSeal support : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic rootBudget →
        Cont rootBudget windows rootWindow →
          Cont rootWindow readback rootReadback →
            Cont rootReadback realSeal rootSeal →
              Cont route cert support →
                PkgSig bundle rootSeal pkg →
                  UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory rootBudget ∧
                      UnaryHistory rootWindow ∧ UnaryHistory rootReadback ∧
                        UnaryHistory rootSeal ∧ UnaryHistory support ∧
                          Cont diagonal dyadic rootBudget ∧
                            Cont rootBudget windows rootWindow ∧
                              Cont rootWindow readback rootReadback ∧
                                Cont rootReadback realSeal rootSeal ∧
                                  Cont route cert support ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle rootSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicRootBudget rootBudgetWindowsRootWindow
    rootWindowReadbackRootReadback rootReadbackRealSealRootSeal routeCertSupport
    rootSealPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootBudgetUnary : UnaryHistory rootBudget :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRootBudget
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed rootBudgetUnary windowsUnary rootBudgetWindowsRootWindow
  have rootReadbackUnary : UnaryHistory rootReadback :=
    unary_cont_closed rootWindowUnary readbackUnary rootWindowReadbackRootReadback
  have rootSealUnary : UnaryHistory rootSeal :=
    unary_cont_closed rootReadbackUnary realSealUnary rootReadbackRealSealRootSeal
  have supportUnary : UnaryHistory support :=
    unary_cont_closed routeUnary certUnary routeCertSupport
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      rootBudgetUnary, rootWindowUnary, rootReadbackUnary, rootSealUnary, supportUnary,
      diagonalDyadicRootBudget, rootBudgetWindowsRootWindow, rootWindowReadbackRootReadback,
      rootReadbackRealSealRootSeal, routeCertSupport, provenancePkg, rootSealPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
