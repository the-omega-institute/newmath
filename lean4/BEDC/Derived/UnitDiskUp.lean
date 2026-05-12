import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnitDiskUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UnitDiskBHistCarrier [AskSetup] [PackageSetup]
    (x y point origin radius bound boundary sameRows route provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory point ∧ UnaryHistory origin ∧
    UnaryHistory radius ∧ UnaryHistory bound ∧ UnaryHistory boundary ∧
      UnaryHistory sameRows ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ UnaryHistory endpoint ∧ hsame point (append x y) ∧
          hsame radius (append point origin) ∧ Cont sameRows route endpoint ∧
            PkgSig bundle endpoint pkg

theorem UnitDiskBHistCarrier_carrier_stability [AskSetup] [PackageSetup]
    {x y point origin radius bound boundary sameRows route provenance nameCert endpoint x' y'
      origin' bound' boundary' sameRows' route' provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnitDiskBHistCarrier x y point origin radius bound boundary sameRows route provenance
        nameCert endpoint bundle pkg ->
      hsame x x' ->
        hsame y y' ->
          hsame origin origin' ->
            hsame bound bound' ->
              hsame boundary boundary' ->
                hsame sameRows sameRows' ->
                  hsame route route' ->
                    hsame provenance provenance' ->
                      hsame nameCert nameCert' ->
                        exists point' radius' endpoint',
                          UnitDiskBHistCarrier x' y' point' origin' radius' bound'
                              boundary' sameRows' route' provenance' nameCert' endpoint'
                              bundle pkg ∧
                            hsame point' (append x' y') ∧
                              hsame radius' (append point' origin') := by
  intro carrier sameX sameY sameOrigin sameBound sameBoundary sameRowsTransport
    sameRoute sameProvenance sameNameCert
  obtain ⟨xUnary, yUnary, _pointUnary, originUnary, _radiusUnary, boundUnary,
    boundaryUnary, sameRowsUnary, routeUnary, provenanceUnary, nameCertUnary, endpointUnary,
    _pointRow, _radiusRow, endpointRow, pkgRow⟩ := carrier
  have xUnary' : UnaryHistory x' :=
    unary_transport xUnary sameX
  have yUnary' : UnaryHistory y' :=
    unary_transport yUnary sameY
  have originUnary' : UnaryHistory origin' :=
    unary_transport originUnary sameOrigin
  have boundUnary' : UnaryHistory bound' :=
    unary_transport boundUnary sameBound
  have boundaryUnary' : UnaryHistory boundary' :=
    unary_transport boundaryUnary sameBoundary
  have sameRowsUnary' : UnaryHistory sameRows' :=
    unary_transport sameRowsUnary sameRowsTransport
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary sameNameCert
  have endpointRow' : Cont sameRows' route' endpoint := by
    cases sameRowsTransport
    cases sameRoute
    exact endpointRow
  let point' : BHist := append x' y'
  let radius' : BHist := append point' origin'
  have pointUnary' : UnaryHistory point' :=
    unary_cont_closed xUnary' yUnary' (rfl : Cont x' y' point')
  have radiusUnary' : UnaryHistory radius' :=
    unary_cont_closed pointUnary' originUnary' (rfl : Cont point' origin' radius')
  exact
    ⟨point', radius', endpoint,
      ⟨xUnary', yUnary', pointUnary', originUnary', radiusUnary', boundUnary',
        boundaryUnary', sameRowsUnary', routeUnary', provenanceUnary', nameCertUnary',
        endpointUnary, rfl, rfl, endpointRow', pkgRow⟩,
      rfl, rfl⟩

end BEDC.Derived.UnitDiskUp
