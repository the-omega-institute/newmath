import BEDC.Derived.DyadicBallUp

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicBallFiniteEnclosure_radius_window_monotonicity [AskSetup] [PackageSetup]
    {center radius schedule observation containment transportWindow regWindow certRow center'
      radius' schedule' observation' containment' transportWindow' regWindow' certRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteEnclosure center radius schedule observation containment transportWindow
        regWindow certRow bundle pkg ->
      hsame center center' ->
        UnaryHistory radius' ->
          hsame schedule schedule' ->
            hsame observation observation' ->
              hsame containment containment' ->
                Cont center' radius' transportWindow' ->
                  Cont observation' containment' regWindow' ->
                    Cont transportWindow' regWindow' certRow' ->
                      PkgSig bundle regWindow' pkg ->
                        DyadicBallFiniteEnclosure center' radius' schedule' observation'
                            containment' transportWindow' regWindow' certRow' bundle pkg ∧
                          Cont center' radius' transportWindow' ∧
                            Cont observation' containment' regWindow' ∧
                              PkgSig bundle regWindow' pkg := by
  intro enclosure sameCenter radiusUnary' sameSchedule sameObservation sameContainment
    transportWindowRow' regWindowRow' certRowRoute' pkgRow'
  obtain ⟨centerUnary, _radiusUnary, scheduleUnary, observationUnary, containmentUnary,
    _transportUnary, _regUnary, _certUnary, _transportWindowRow, _regWindowRow,
    _certRowRoute, _pkgRow⟩ := enclosure
  have centerUnary' : UnaryHistory center' :=
    unary_transport centerUnary sameCenter
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary sameObservation
  have containmentUnary' : UnaryHistory containment' :=
    unary_transport containmentUnary sameContainment
  have transportWindowUnary' : UnaryHistory transportWindow' :=
    unary_cont_closed centerUnary' radiusUnary' transportWindowRow'
  have regWindowUnary' : UnaryHistory regWindow' :=
    unary_cont_closed observationUnary' containmentUnary' regWindowRow'
  have certRowUnary' : UnaryHistory certRow' :=
    unary_cont_closed transportWindowUnary' regWindowUnary' certRowRoute'
  exact
    ⟨⟨centerUnary', radiusUnary', scheduleUnary', observationUnary', containmentUnary',
        transportWindowUnary', regWindowUnary', certRowUnary', transportWindowRow',
        regWindowRow', certRowRoute', pkgRow'⟩,
      transportWindowRow', regWindowRow', pkgRow'⟩

theorem DyadicBallFiniteWindowPacket_radius_window_monotonicity [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance certRow handoff
      sealBoundary narrowedRadius narrowedSchedule narrowedObservation narrowedContainment
      narrowedRoute narrowedHandoff narrowedCertRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteWindowPacket center radius schedule observation containment route
        provenance certRow handoff sealBoundary bundle pkg ->
      UnaryHistory narrowedRadius ->
        hsame schedule narrowedSchedule ->
          hsame observation narrowedObservation ->
            Cont center narrowedRadius narrowedContainment ->
              Cont narrowedSchedule narrowedObservation narrowedRoute ->
                Cont narrowedContainment narrowedRoute narrowedHandoff ->
                  Cont narrowedHandoff provenance narrowedCertRow ->
                    Cont narrowedHandoff sealBoundary narrowedCertRow ->
                      PkgSig bundle narrowedHandoff pkg ->
                        DyadicBallFiniteWindowPacket center narrowedRadius narrowedSchedule
                            narrowedObservation narrowedContainment narrowedRoute provenance
                            narrowedCertRow narrowedHandoff sealBoundary bundle pkg ∧
                          hsame narrowedRoute (append narrowedSchedule narrowedObservation) ∧
                            hsame narrowedHandoff
                              (append narrowedContainment narrowedRoute) := by
  intro packet narrowedRadiusUnary sameSchedule sameObservation narrowedContainmentRow
  intro narrowedRouteRow narrowedHandoffRow narrowedProvenanceRow narrowedSealRow narrowedPkg
  obtain ⟨centerUnary, _radiusUnary, scheduleUnary, observationUnary, provenanceUnary,
    _certUnary, sealUnary, _containmentRow, _routeRow, _handoffRow, _provenanceRow,
    _sealRow, _pkgRow⟩ := packet
  have narrowedScheduleUnary : UnaryHistory narrowedSchedule :=
    unary_transport scheduleUnary sameSchedule
  have narrowedObservationUnary : UnaryHistory narrowedObservation :=
    unary_transport observationUnary sameObservation
  have narrowedContainmentUnary : UnaryHistory narrowedContainment :=
    unary_cont_closed centerUnary narrowedRadiusUnary narrowedContainmentRow
  have narrowedRouteUnary : UnaryHistory narrowedRoute :=
    unary_cont_closed narrowedScheduleUnary narrowedObservationUnary narrowedRouteRow
  have narrowedHandoffUnary : UnaryHistory narrowedHandoff :=
    unary_cont_closed narrowedContainmentUnary narrowedRouteUnary narrowedHandoffRow
  have narrowedCertUnary : UnaryHistory narrowedCertRow :=
    unary_cont_closed narrowedHandoffUnary provenanceUnary narrowedProvenanceRow
  exact
    ⟨⟨centerUnary, narrowedRadiusUnary, narrowedScheduleUnary, narrowedObservationUnary,
        provenanceUnary, narrowedCertUnary, sealUnary, narrowedContainmentRow,
        narrowedRouteRow, narrowedHandoffRow, narrowedProvenanceRow, narrowedSealRow,
        narrowedPkg⟩,
      narrowedRouteRow, narrowedHandoffRow⟩

end BEDC.Derived.DyadicBallUp
