import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCompletionConsumerPackage [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget endpoint completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows budgetPrefix ->
        Cont budgetPrefix sealRow sealBudget ->
          Cont readback realSeal endpoint ->
            Cont endpoint cert completion ->
              PkgSig bundle sealBudget pkg ->
                PkgSig bundle endpoint pkg ->
                  PkgSig bundle completion pkg ->
                    UnaryHistory budgetPrefix ∧ UnaryHistory sealBudget ∧
                      UnaryHistory endpoint ∧ UnaryHistory completion ∧
                        Cont dyadic windows budgetPrefix ∧
                          Cont budgetPrefix sealRow sealBudget ∧
                            Cont readback realSeal endpoint ∧
                              Cont endpoint cert completion ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle sealBudget pkg ∧
                                    PkgSig bundle endpoint pkg ∧
                                      PkgSig bundle completion pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealRow readbackEndpoint
    endpointCertCompletion sealBudgetPkg endpointPkg completionPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealUnary budgetPrefixSealRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed endpointUnary certUnary endpointCertCompletion
  exact
    ⟨budgetPrefixUnary, sealBudgetUnary, endpointUnary, completionUnary,
      dyadicWindowsBudgetPrefix, budgetPrefixSealRow, readbackEndpoint,
      endpointCertCompletion, provenancePkg, sealBudgetPkg, endpointPkg, completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
