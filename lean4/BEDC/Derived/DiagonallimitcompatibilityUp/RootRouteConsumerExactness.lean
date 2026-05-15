import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteConsumerExactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows budgetPrefix ->
        Cont budgetPrefix sealRow sealBudget ->
          Cont readback realSeal endpoint ->
            Cont sealBudget endpoint consumer ->
              PkgSig bundle sealBudget pkg ->
                PkgSig bundle endpoint pkg ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
                      UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory budgetPrefix ∧
                        UnaryHistory sealBudget ∧ UnaryHistory readback ∧
                          UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
                            UnaryHistory consumer ∧ Cont dyadic windows budgetPrefix ∧
                              Cont budgetPrefix sealRow sealBudget ∧
                                Cont readback realSeal endpoint ∧
                                  Cont sealBudget endpoint consumer ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle sealBudget pkg ∧
                                        PkgSig bundle endpoint pkg ∧
                                          PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicWindowsBudget budgetPrefixSeal readbackEndpoint sealEndpointConsumer
    sealBudgetPkg endpointPkg consumerPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudget
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealUnary budgetPrefixSeal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealBudgetUnary endpointUnary sealEndpointConsumer
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, budgetPrefixUnary,
      sealBudgetUnary, readbackUnary, realSealUnary, endpointUnary, consumerUnary,
      dyadicWindowsBudget, budgetPrefixSeal, readbackEndpoint, sealEndpointConsumer,
      provenancePkg, sealBudgetPkg, endpointPkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
