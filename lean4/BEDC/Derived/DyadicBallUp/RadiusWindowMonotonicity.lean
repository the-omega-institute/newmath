import BEDC.Derived.DyadicBallUp

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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
