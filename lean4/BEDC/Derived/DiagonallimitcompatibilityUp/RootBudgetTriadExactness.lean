import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_root_budget_triad_exactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetSource budgetPrefix sealBudget endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetSource ->
        Cont dyadic windows budgetPrefix ->
          Cont budgetPrefix sealRow sealBudget ->
            Cont readback realSeal endpoint ->
              PkgSig bundle budgetSource pkg ->
                PkgSig bundle sealBudget pkg ->
                  PkgSig bundle endpoint pkg ->
                    UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                      UnaryHistory readback ∧ UnaryHistory realSeal ∧
                        UnaryHistory budgetSource ∧ UnaryHistory budgetPrefix ∧
                          UnaryHistory sealBudget ∧ UnaryHistory endpoint ∧
                            Cont diagonal dyadic budgetSource ∧
                              Cont dyadic windows budgetPrefix ∧
                                Cont budgetPrefix sealRow sealBudget ∧
                                  Cont readback realSeal endpoint ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle budgetSource pkg ∧
                                        PkgSig bundle sealBudget pkg ∧
                                          PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalDyadicBudgetSource dyadicWindowsBudgetPrefix
    budgetPrefixSealBudget readbackRealSealEndpoint budgetSourcePkg sealBudgetPkg
    endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSealRow, _dyadicWindowsReadback,
    _readbackRealSealRoute, _routeCertTransport, provenancePkg⟩ := carrier
  have budgetSourceUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetSource
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealRowUnary budgetPrefixSealBudget
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEndpoint
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      budgetSourceUnary, budgetPrefixUnary, sealBudgetUnary, endpointUnary,
      diagonalDyadicBudgetSource, dyadicWindowsBudgetPrefix, budgetPrefixSealBudget,
      readbackRealSealEndpoint, provenancePkg, budgetSourcePkg, sealBudgetPkg,
      endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
