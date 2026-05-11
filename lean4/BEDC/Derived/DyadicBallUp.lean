import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicBallPacket [AskSetup] [PackageSetup]
    (center radius schedule observation containment route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory schedule ∧
    UnaryHistory observation ∧ UnaryHistory containment ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont center radius schedule ∧
        Cont schedule observation containment ∧ Cont containment route endpoint ∧
          PkgSig bundle endpoint pkg

theorem DyadicBallPacket_classifier_laws [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance endpoint center' radius'
      schedule' observation' containment' route' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallPacket center radius schedule observation containment route provenance endpoint
        bundle pkg ->
      hsame center center' ->
        hsame radius radius' ->
          hsame observation observation' ->
            hsame route route' ->
              hsame provenance provenance' ->
                Cont center' radius' schedule' ->
                  Cont schedule' observation' containment' ->
                    Cont containment' route' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        DyadicBallPacket center' radius' schedule' observation' containment'
                            route' provenance' endpoint' bundle pkg ∧
                          hsame schedule schedule' ∧ hsame containment containment' ∧
                            hsame endpoint endpoint' := by
  intro packet sameCenter sameRadius sameObservation sameRoute sameProvenance
    targetSchedule targetContainment targetEndpoint targetPkg
  have centerUnary : UnaryHistory center :=
    packet.left
  have radiusUnary : UnaryHistory radius :=
    packet.right.left
  have observationUnary : UnaryHistory observation :=
    packet.right.right.right.left
  have routeUnary : UnaryHistory route :=
    packet.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.right.right.left
  have sourceSchedule : Cont center radius schedule :=
    packet.right.right.right.right.right.right.right.right.left
  have sourceContainment : Cont schedule observation containment :=
    packet.right.right.right.right.right.right.right.right.right.left
  have sourceEndpoint : Cont containment route endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have centerUnary' : UnaryHistory center' :=
    unary_transport centerUnary sameCenter
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_cont_closed centerUnary' radiusUnary' targetSchedule
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary sameObservation
  have containmentUnary' : UnaryHistory containment' :=
    unary_cont_closed scheduleUnary' observationUnary' targetContainment
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed containmentUnary' routeUnary' targetEndpoint
  have sameSchedule : hsame schedule schedule' :=
    cont_respects_hsame sameCenter sameRadius sourceSchedule targetSchedule
  have sameContainment : hsame containment containment' :=
    cont_respects_hsame sameSchedule sameObservation sourceContainment targetContainment
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameContainment sameRoute sourceEndpoint targetEndpoint
  exact
    ⟨⟨centerUnary', radiusUnary', scheduleUnary', observationUnary', containmentUnary',
        routeUnary', provenanceUnary', endpointUnary', targetSchedule, targetContainment,
        targetEndpoint, targetPkg⟩,
      sameSchedule, sameContainment, sameEndpoint⟩

theorem DyadicBallPacket_radius_refinement_closure [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance endpoint radius'
      containment' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallPacket center radius schedule observation containment route provenance endpoint
        bundle pkg →
      UnaryHistory radius' →
        Cont center radius' schedule →
          Cont schedule observation containment' →
            Cont containment' route endpoint' →
              PkgSig bundle endpoint' pkg →
                DyadicBallPacket center radius' schedule observation containment' route
                  provenance endpoint' bundle pkg := by
  intro packet radiusUnary' refinedSchedule refinedContainment refinedEndpoint refinedPkg
  have centerUnary : UnaryHistory center :=
    packet.left
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.left
  have observationUnary : UnaryHistory observation :=
    packet.right.right.right.left
  have routeUnary : UnaryHistory route :=
    packet.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.right.right.left
  have containmentUnary' : UnaryHistory containment' :=
    unary_cont_closed scheduleUnary observationUnary refinedContainment
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed containmentUnary' routeUnary refinedEndpoint
  exact
    ⟨centerUnary, radiusUnary', scheduleUnary, observationUnary, containmentUnary', routeUnary,
      provenanceUnary, endpointUnary', refinedSchedule, refinedContainment, refinedEndpoint,
      refinedPkg⟩

end BEDC.Derived.DyadicBallUp
