import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_synchronizer_observation_route_uniqueness
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      request sealBudget tail selector compatibility locked observation obsRoute obsRoute' endpoint
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory request -> UnaryHistory tail -> UnaryHistory compatibility ->
        UnaryHistory observation ->
          Cont sealRow request sealBudget -> Cont sealBudget tail selector ->
            Cont selector compatibility locked ->
              Cont locked observation obsRoute -> Cont locked observation obsRoute' ->
                Cont obsRoute realSeal endpoint -> Cont obsRoute' realSeal endpoint' ->
                  PkgSig bundle endpoint pkg -> PkgSig bundle endpoint' pkg ->
                    hsame obsRoute obsRoute' ∧ hsame endpoint endpoint' ∧
                      UnaryHistory endpoint ∧ UnaryHistory endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier requestUnary tailUnary compatibilityUnary observationUnary sealRowRequestSealBudget
    sealBudgetTailSelector selectorCompatibilityLocked lockedObservationObsRoute
    lockedObservationObsRoute' obsRouteRealSealEndpoint obsRoute'RealSealEndpoint'
    _endpointPkg _endpointPkg'
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed sealRowUnary requestUnary sealRowRequestSealBudget
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed sealBudgetUnary tailUnary sealBudgetTailSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary compatibilityUnary selectorCompatibilityLocked
  have obsRouteUnary : UnaryHistory obsRoute :=
    unary_cont_closed lockedUnary observationUnary lockedObservationObsRoute
  have obsRoute'Unary : UnaryHistory obsRoute' :=
    unary_cont_closed lockedUnary observationUnary lockedObservationObsRoute'
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed obsRouteUnary realSealUnary obsRouteRealSealEndpoint
  have endpoint'Unary : UnaryHistory endpoint' :=
    unary_cont_closed obsRoute'Unary realSealUnary obsRoute'RealSealEndpoint'
  have sameObsRoute : hsame obsRoute obsRoute' :=
    cont_respects_hsame (hsame_refl locked) (hsame_refl observation)
      lockedObservationObsRoute lockedObservationObsRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameObsRoute (hsame_refl realSeal) obsRouteRealSealEndpoint
      obsRoute'RealSealEndpoint'
  exact ⟨sameObsRoute, sameEndpoint, endpointUnary, endpoint'Unary⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
