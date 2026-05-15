import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_tail_budget_observation_lock
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      request sealBudget tailSchedule selector compatibility locked observation observed
      tailRoute endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory request ->
        UnaryHistory tailSchedule ->
          UnaryHistory compatibility ->
            UnaryHistory observation ->
              Cont sealRow request sealBudget ->
                Cont sealBudget tailSchedule selector ->
                  Cont selector compatibility locked ->
                    Cont locked observation observed ->
                      Cont observed readback tailRoute ->
                        Cont tailRoute realSeal endpoint ->
                          PkgSig bundle locked pkg ->
                            PkgSig bundle endpoint pkg ->
                              UnaryHistory sealRow ∧ UnaryHistory request ∧
                                UnaryHistory sealBudget ∧ UnaryHistory tailSchedule ∧
                                  UnaryHistory selector ∧ UnaryHistory compatibility ∧
                                    UnaryHistory locked ∧ UnaryHistory observation ∧
                                      UnaryHistory observed ∧ UnaryHistory tailRoute ∧
                                        UnaryHistory endpoint ∧
                                          Cont sealRow request sealBudget ∧
                                            Cont sealBudget tailSchedule selector ∧
                                              Cont selector compatibility locked ∧
                                                Cont locked observation observed ∧
                                                  Cont observed readback tailRoute ∧
                                                    Cont tailRoute realSeal endpoint ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle locked pkg ∧
                                                          PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier requestUnary tailScheduleUnary compatibilityUnary observationUnary
    sealRowRequestSealBudget sealBudgetTailScheduleSelector selectorCompatibilityLocked
    lockedObservationObserved observedReadbackTailRoute tailRouteRealSealEndpoint lockedPkg
    endpointPkg
  have handoff :=
    DiagonalLimitCompatibilityCarrier_seal_budget_synchronizer_handoff carrier requestUnary
      tailScheduleUnary compatibilityUnary sealRowRequestSealBudget sealBudgetTailScheduleSelector
      selectorCompatibilityLocked lockedPkg
  obtain ⟨sealRowUnary, requestUnaryOut, sealBudgetUnary, tailScheduleUnaryOut,
    selectorUnary, compatibilityUnaryOut, lockedUnary, sealRowRequestSealBudgetOut,
    sealBudgetTailScheduleSelectorOut, selectorCompatibilityLockedOut, provenancePkg,
    lockedPkgOut⟩ := handoff
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnaryFromCarrier, _dyadicUnary,
    _windowsUnary, readbackUnary, realSealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback,
    _readbackRealSealRoute, _routeCertTransport, _provenancePkgFromCarrier⟩ := carrier
  have observedUnary : UnaryHistory observed :=
    unary_cont_closed lockedUnary observationUnary lockedObservationObserved
  have tailRouteUnary : UnaryHistory tailRoute :=
    unary_cont_closed observedUnary readbackUnary observedReadbackTailRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed tailRouteUnary realSealUnary tailRouteRealSealEndpoint
  exact
    ⟨sealRowUnary, requestUnaryOut, sealBudgetUnary, tailScheduleUnaryOut, selectorUnary,
      compatibilityUnaryOut, lockedUnary, observationUnary, observedUnary, tailRouteUnary,
      endpointUnary, sealRowRequestSealBudgetOut, sealBudgetTailScheduleSelectorOut,
      selectorCompatibilityLockedOut, lockedObservationObserved, observedReadbackTailRoute,
      tailRouteRealSealEndpoint, provenancePkg, lockedPkgOut, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
