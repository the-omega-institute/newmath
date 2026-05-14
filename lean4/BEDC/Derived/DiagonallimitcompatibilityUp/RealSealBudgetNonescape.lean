import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_real_seal_budget_nonescape
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      request sealBudget tail selector compatibility locked endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory request ->
        UnaryHistory tail ->
          UnaryHistory compatibility ->
            Cont sealRow request sealBudget ->
              Cont sealBudget tail selector ->
                Cont selector compatibility locked ->
                  Cont readback realSeal endpoint ->
                    PkgSig bundle locked pkg ->
                      PkgSig bundle endpoint pkg ->
                        UnaryHistory sealRow ∧ UnaryHistory request ∧
                          UnaryHistory sealBudget ∧ UnaryHistory tail ∧
                            UnaryHistory selector ∧ UnaryHistory compatibility ∧
                              UnaryHistory locked ∧ UnaryHistory endpoint ∧
                                Cont sealRow request sealBudget ∧
                                  Cont sealBudget tail selector ∧
                                    Cont selector compatibility locked ∧
                                      Cont readback realSeal endpoint ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle locked pkg ∧
                                            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier requestUnary tailUnary compatibilityUnary sealRowRequestSealBudget
    sealBudgetTailSelector selectorCompatibilityLocked readbackRealSealEndpoint lockedPkg
    endpointPkg
  have handoff :=
    DiagonalLimitCompatibilityCarrier_seal_budget_synchronizer_handoff carrier requestUnary
      tailUnary compatibilityUnary sealRowRequestSealBudget sealBudgetTailSelector
      selectorCompatibilityLocked lockedPkg
  obtain ⟨sealRowUnary, requestUnaryOut, sealBudgetUnary, tailUnaryOut, selectorUnary,
    compatibilityUnaryOut, lockedUnary, sealRowRequestSealBudgetOut,
    sealBudgetTailSelectorOut, selectorCompatibilityLockedOut, provenancePkg,
    lockedPkgOut⟩ := handoff
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnaryFromCarrier, _dyadicUnary,
    _windowsUnary, readbackUnary, realSealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback,
    _readbackRealSealRoute, _routeCertTransport, _provenancePkgFromCarrier⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEndpoint
  exact
    ⟨sealRowUnary, requestUnaryOut, sealBudgetUnary, tailUnaryOut, selectorUnary,
      compatibilityUnaryOut, lockedUnary, endpointUnary, sealRowRequestSealBudgetOut,
      sealBudgetTailSelectorOut, selectorCompatibilityLockedOut, readbackRealSealEndpoint,
      provenancePkg, lockedPkgOut, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
