import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_synchronizer_observation_cofinal_pullback
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      locked observation observed observed' tailRoute tailRoute' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory observation ->
        Cont locked observation observed ->
          Cont locked observation observed' ->
            Cont observed readback tailRoute ->
              Cont observed' readback tailRoute' ->
                Cont tailRoute realSeal endpoint ->
                  Cont tailRoute' realSeal endpoint' ->
                    PkgSig bundle endpoint pkg ->
                      PkgSig bundle endpoint' pkg ->
                        hsame observed observed' ∧ hsame tailRoute tailRoute' ∧
                          hsame endpoint endpoint' ∧ PkgSig bundle endpoint pkg ∧
                            PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame UnaryHistory
  intro carrier _observationUnary lockedObservationObserved lockedObservationObserved'
    observedReadbackTailRoute observedReadbackTailRoute' tailRouteRealSealEndpoint
    tailRouteRealSealEndpoint' endpointPkg endpointPkg'
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have sameObserved : hsame observed observed' :=
    cont_respects_hsame (hsame_refl locked) (hsame_refl observation)
      lockedObservationObserved lockedObservationObserved'
  have sameTailRoute : hsame tailRoute tailRoute' :=
    cont_respects_hsame sameObserved (hsame_refl readback) observedReadbackTailRoute
      observedReadbackTailRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameTailRoute (hsame_refl realSeal) tailRouteRealSealEndpoint
      tailRouteRealSealEndpoint'
  exact ⟨sameObserved, sameTailRoute, sameEndpoint, endpointPkg, endpointPkg'⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
