import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnitDiskUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem UnitDiskOriginRows_radius_ledger [AskSetup] [PackageSetup]
    {x y origin bound boundary sameRows route provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory x ->
      UnaryHistory y ->
        UnaryHistory origin ->
          UnaryHistory bound ->
            UnaryHistory boundary ->
              UnaryHistory sameRows ->
                UnaryHistory route ->
                  UnaryHistory provenance ->
                    UnaryHistory nameCert ->
                      UnaryHistory endpoint ->
                        Cont sameRows route endpoint ->
                          PkgSig bundle endpoint pkg ->
                            UnitDiskBHistCarrier x y (append x y) origin
                                (append (append x y) origin) bound boundary sameRows route
                                provenance nameCert endpoint bundle pkg ∧
                              hsame (append (append x y) origin)
                                (append (append x y) origin) := by
  intro xUnary yUnary originUnary boundUnary boundaryUnary sameRowsUnary routeUnary
    provenanceUnary nameCertUnary endpointUnary routeEndpoint pkgEndpoint
  have pointUnary : UnaryHistory (append x y) :=
    unary_cont_closed xUnary yUnary (rfl : Cont x y (append x y))
  have radiusUnary : UnaryHistory (append (append x y) origin) :=
    unary_cont_closed pointUnary originUnary
      (rfl : Cont (append x y) origin (append (append x y) origin))
  constructor
  · exact
      ⟨xUnary, yUnary, pointUnary, originUnary, radiusUnary, boundUnary, boundaryUnary,
        sameRowsUnary, routeUnary, provenanceUnary, nameCertUnary, endpointUnary, rfl, rfl,
        routeEndpoint, pkgEndpoint⟩
  · rfl

theorem UnitDiskBHistCarrier_boundary_sone_consumer [AskSetup] [PackageSetup]
    {x y point origin radius bound boundary sameRows route provenance nameCert endpoint
      boundaryConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnitDiskBHistCarrier x y point origin radius bound boundary sameRows route provenance
        nameCert endpoint bundle pkg ->
      Cont boundary route boundaryConsumer ->
        PkgSig bundle boundaryConsumer pkg ->
          UnaryHistory boundary ∧ UnaryHistory route ∧ UnaryHistory boundaryConsumer ∧
            hsame point (append x y) ∧ hsame radius (append point origin) ∧
              Cont boundary route boundaryConsumer ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle boundaryConsumer pkg := by
  intro carrier boundaryRouteConsumer boundaryConsumerPkg
  obtain ⟨_xUnary, _yUnary, _pointUnary, _originUnary, _radiusUnary, _boundUnary,
    boundaryUnary, _sameRowsUnary, routeUnary, _provenanceUnary, _nameCertUnary,
      _endpointUnary, pointRows, radiusRows, _endpointRoute, endpointPkg⟩ := carrier
  have boundaryConsumerUnary : UnaryHistory boundaryConsumer :=
    unary_cont_closed boundaryUnary routeUnary boundaryRouteConsumer
  exact
    ⟨boundaryUnary, routeUnary, boundaryConsumerUnary, pointRows, radiusRows,
      boundaryRouteConsumer, endpointPkg, boundaryConsumerPkg⟩

theorem UnitDiskBHistCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {x y point origin radius bound boundary sameRows route provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnitDiskBHistCarrier x y point origin radius bound boundary sameRows route provenance
        nameCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          UnitDiskBHistCarrier x y point origin radius bound boundary sameRows route provenance
            nameCert endpoint bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          UnitDiskBHistCarrier x y point origin radius bound boundary sameRows route provenance
            nameCert endpoint bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          UnitDiskBHistCarrier x y point origin radius bound boundary sameRows route provenance
            nameCert endpoint bundle pkg ∧ hsame row nameCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnitDiskBHistCarrier hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro nameCert (And.intro carrier (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.UnitDiskUp
