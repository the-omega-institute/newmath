import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySealBudgetRouteExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows budgetPrefix →
        Cont budgetPrefix sealRow sealBudget →
          Cont readback realSeal endpoint →
            PkgSig bundle sealBudget pkg →
              PkgSig bundle endpoint pkg →
                UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory budgetPrefix ∧
                  UnaryHistory sealRow ∧ UnaryHistory sealBudget ∧ UnaryHistory readback ∧
                    UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
                      Cont dyadic windows budgetPrefix ∧
                        Cont budgetPrefix sealRow sealBudget ∧
                          Cont readback realSeal endpoint ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle sealBudget pkg ∧
                              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealRow readbackEndpoint sealBudgetPkg
    endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealUnary budgetPrefixSealRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨dyadicUnary, windowsUnary, budgetPrefixUnary, sealUnary, sealBudgetUnary,
      readbackUnary, realSealUnary, endpointUnary, dyadicWindowsBudgetPrefix,
      budgetPrefixSealRow, readbackEndpoint, provenancePkg, sealBudgetPkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
