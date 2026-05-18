import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCompletionSealBudget [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetSource completionSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetSource ->
        Cont budgetSource windows readback ->
          Cont readback realSeal completionSeal ->
            PkgSig bundle completionSeal pkg ->
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory budgetSource ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                  UnaryHistory completionSeal ∧ Cont diagonal dyadic budgetSource ∧
                    Cont budgetSource windows readback ∧
                      Cont readback realSeal completionSeal ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle completionSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier diagonalDyadicBudget budgetWindowsReadback readbackRealCompletion
    completionPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudget
  have completionUnary : UnaryHistory completionSeal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealCompletion
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, budgetUnary, readbackUnary, realSealUnary,
      completionUnary, diagonalDyadicBudget, budgetWindowsReadback, readbackRealCompletion,
      provenancePkg, completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
