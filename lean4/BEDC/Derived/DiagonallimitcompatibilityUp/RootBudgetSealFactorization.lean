import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_budget_seal_factorization
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetSource sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetSource ->
        Cont readback realSeal sealEndpoint ->
          PkgSig bundle sealEndpoint pkg ->
            UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
              UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory budgetSource ∧
                UnaryHistory sealEndpoint ∧ Cont diagonal dyadic budgetSource ∧
                  Cont dyadic windows readback ∧ Cont readback realSeal sealEndpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle sealEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalDyadicBudgetSource readbackRealSealSealEndpoint sealEndpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetSourceUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetSource
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealSealEndpoint
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      budgetSourceUnary, sealEndpointUnary, diagonalDyadicBudgetSource,
      dyadicWindowsReadback, readbackRealSealSealEndpoint, provenancePkg, sealEndpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
