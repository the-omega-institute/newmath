import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteClassifierExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget endpoint classifierRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows budgetPrefix ->
        Cont budgetPrefix sealRow sealBudget ->
          Cont readback realSeal endpoint ->
            Cont sealBudget endpoint classifierRead ->
              PkgSig bundle sealBudget pkg ->
                PkgSig bundle endpoint pkg ->
                  PkgSig bundle classifierRead pkg ->
                    UnaryHistory classifierRead ∧ Cont dyadic windows budgetPrefix ∧
                      Cont budgetPrefix sealRow sealBudget ∧
                        Cont readback realSeal endpoint ∧
                          Cont sealBudget endpoint classifierRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle classifierRead pkg ∧
                              (Cont classifierRead (BHist.e0 hostTail) sealBudget -> False) ∧
                                (Cont classifierRead (BHist.e1 hostTail) endpoint -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealRow readbackEndpoint
    sealBudgetEndpointClassifier _sealBudgetPkg _endpointPkg classifierPkg
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
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed sealBudgetUnary endpointUnary sealBudgetEndpointClassifier
  exact
    ⟨classifierUnary, dyadicWindowsBudgetPrefix, budgetPrefixSealRow, readbackEndpoint,
      sealBudgetEndpointClassifier, provenancePkg, classifierPkg,
      (fun backToSeal =>
        cont_mutual_extension_right_tail_absurd.left sealBudgetEndpointClassifier backToSeal),
      (fun backToEndpoint =>
        let endpointSealBudgetClassifier : Cont endpoint sealBudget classifierRead :=
          cont_result_hsame_transport
            (cont_intro (h := endpoint) (k := sealBudget) rfl)
            (hsame_symm
              (unary_cont_comm sealBudgetUnary endpointUnary sealBudgetEndpointClassifier
                (cont_intro (h := endpoint) (k := sealBudget) rfl)))
        cont_mutual_extension_right_tail_absurd.right endpointSealBudgetClassifier
          backToEndpoint)⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
