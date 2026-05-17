import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_root_route_seal_readback_classifier
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget endpoint classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows budgetPrefix ->
        Cont budgetPrefix sealRow sealBudget ->
          Cont readback realSeal endpoint ->
            Cont sealBudget endpoint classifierRead ->
              PkgSig bundle classifierRead pkg ->
                UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory budgetPrefix ∧
                  UnaryHistory sealRow ∧ UnaryHistory sealBudget ∧ UnaryHistory readback ∧
                    UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
                      UnaryHistory classifierRead ∧ Cont dyadic windows budgetPrefix ∧
                        Cont budgetPrefix sealRow sealBudget ∧ Cont readback realSeal endpoint ∧
                          Cont sealBudget endpoint classifierRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealRow readbackRealSealEndpoint
    sealBudgetEndpointClassifier classifierPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealRowUnary budgetPrefixSealRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEndpoint
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed sealBudgetUnary endpointUnary sealBudgetEndpointClassifier
  exact
    ⟨dyadicUnary, windowsUnary, budgetPrefixUnary, sealRowUnary, sealBudgetUnary,
      readbackUnary, realSealUnary, endpointUnary, classifierReadUnary,
      dyadicWindowsBudgetPrefix, budgetPrefixSealRow, readbackRealSealEndpoint,
      sealBudgetEndpointClassifier, provenancePkg, classifierPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
