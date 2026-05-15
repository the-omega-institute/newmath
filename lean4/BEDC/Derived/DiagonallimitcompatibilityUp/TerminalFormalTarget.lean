import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_terminal_formal_target [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootBudget rootWindow rootReadback rootSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic rootBudget ->
        Cont rootBudget windows rootWindow ->
          Cont rootWindow readback rootReadback ->
            Cont rootReadback realSeal rootSeal ->
              PkgSig bundle rootSeal pkg ->
                UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                  UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                    UnaryHistory rootBudget ∧ UnaryHistory rootWindow ∧
                      UnaryHistory rootReadback ∧ UnaryHistory rootSeal ∧
                        Cont diagonal triangle sealRow ∧ Cont diagonal dyadic rootBudget ∧
                          Cont rootBudget windows rootWindow ∧
                            Cont rootWindow readback rootReadback ∧
                              Cont rootReadback realSeal rootSeal ∧
                                Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle rootSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicRootBudget rootBudgetWindowsRootWindow
    rootWindowReadbackRootReadback rootReadbackRealSealRootSeal rootSealPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have rootBudgetUnary : UnaryHistory rootBudget :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRootBudget
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed rootBudgetUnary windowsUnary rootBudgetWindowsRootWindow
  have rootReadbackUnary : UnaryHistory rootReadback :=
    unary_cont_closed rootWindowUnary readbackUnary rootWindowReadbackRootReadback
  have rootSealUnary : UnaryHistory rootSeal :=
    unary_cont_closed rootReadbackUnary realSealUnary rootReadbackRealSealRootSeal
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      rootBudgetUnary, rootWindowUnary, rootReadbackUnary, rootSealUnary, diagonalTriangleSeal,
      diagonalDyadicRootBudget, rootBudgetWindowsRootWindow, rootWindowReadbackRootReadback,
      rootReadbackRealSealRootSeal, routeCertTransport, provenancePkg, rootSealPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
