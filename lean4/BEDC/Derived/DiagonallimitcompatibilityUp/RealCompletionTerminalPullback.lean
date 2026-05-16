import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRealCompletionTerminalPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      completion branch pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal completion ->
        UnaryHistory branch ->
          Cont completion branch pullback ->
            PkgSig bundle pullback pkg ->
              UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                  UnaryHistory completion ∧ UnaryHistory branch ∧ UnaryHistory pullback ∧
                    Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                      Cont readback realSeal completion ∧ Cont completion branch pullback ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier readbackRealSealCompletion branchUnary completionBranchPullback pullbackPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealCompletion
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed completionUnary branchUnary completionBranchPullback
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      completionUnary, branchUnary, pullbackUnary, diagonalTriangleSeal, dyadicWindowsReadback,
      readbackRealSealCompletion, completionBranchPullback, provenancePkg, pullbackPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
