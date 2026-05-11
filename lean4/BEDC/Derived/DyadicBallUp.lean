import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem DyadicBallPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallPacket center radius schedule observation containment route provenance endpoint
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicBallPacket center radius schedule observation containment route provenance endpoint
              bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          DyadicBallPacket center radius schedule observation containment route provenance endpoint
              bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          DyadicBallPacket center radius schedule observation containment route provenance endpoint
              bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨packet, hsame_refl endpoint⟩
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same carrier
        exact ⟨carrier.left, hsame_trans (hsame_symm same) carrier.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

def DyadicBallRegSeqRatWindow [AskSetup] [PackageSetup]
    (center radius schedule observation containment transportWindow regWindow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory schedule ∧
    UnaryHistory observation ∧ UnaryHistory containment ∧ UnaryHistory transportWindow ∧
      UnaryHistory regWindow ∧ Cont center radius transportWindow ∧
        Cont observation containment regWindow ∧ PkgSig bundle regWindow pkg

def DyadicBallFiniteEnclosure [AskSetup] [PackageSetup]
    (center radius schedule observation containment transportWindow regWindow certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory schedule ∧
    UnaryHistory observation ∧ UnaryHistory containment ∧ UnaryHistory transportWindow ∧
      UnaryHistory regWindow ∧ UnaryHistory certRow ∧
        Cont center radius transportWindow ∧ Cont observation containment regWindow ∧
          Cont transportWindow regWindow certRow ∧ PkgSig bundle regWindow pkg

theorem DyadicBallFiniteEnclosure_regseqrat_window_handoff [AskSetup] [PackageSetup]
    {center radius schedule observation containment transportWindow regWindow certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteEnclosure center radius schedule observation containment transportWindow
        regWindow certRow bundle pkg ->
      DyadicBallRegSeqRatWindow center radius schedule observation containment transportWindow
          regWindow bundle pkg ∧
        Cont center radius transportWindow ∧ Cont observation containment regWindow ∧
          PkgSig bundle regWindow pkg := by
  intro packet
  obtain ⟨centerUnary, radiusUnary, scheduleUnary, observationUnary, containmentUnary,
    transportUnary, regUnary, _certUnary, centerRadiusRoute, observationContainmentRoute,
    _certRoute, pkgRow⟩ := packet
  exact
    ⟨⟨centerUnary, radiusUnary, scheduleUnary, observationUnary, containmentUnary,
        transportUnary, regUnary, centerRadiusRoute, observationContainmentRoute, pkgRow⟩,
      centerRadiusRoute, observationContainmentRoute, pkgRow⟩

def DyadicBallFiniteWindowPacket [AskSetup] [PackageSetup]
    (center radius schedule observation containment route provenance certRow handoff
      sealBoundary : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory schedule ∧
    UnaryHistory observation ∧ UnaryHistory provenance ∧ UnaryHistory certRow ∧
      UnaryHistory sealBoundary ∧ Cont center radius containment ∧
        Cont schedule observation route ∧ Cont containment route handoff ∧
          Cont handoff provenance certRow ∧ Cont handoff sealBoundary certRow ∧
            PkgSig bundle handoff pkg

theorem DyadicBallFiniteWindowPacket_regseqrat_window_handoff [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance certRow handoff
      sealBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteWindowPacket center radius schedule observation containment route
        provenance certRow handoff sealBoundary bundle pkg ->
      UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory schedule ∧
        UnaryHistory observation ∧ UnaryHistory containment ∧ UnaryHistory route ∧
          UnaryHistory handoff ∧ hsame containment (append center radius) ∧
            hsame route (append schedule observation) ∧
              hsame handoff (append containment route) ∧ PkgSig bundle handoff pkg := by
  intro packet
  obtain ⟨centerUnary, radiusUnary, scheduleUnary, observationUnary, _provenanceUnary,
    _certUnary, _sealUnary, containmentRow, routeRow, handoffRow, _provenanceRow,
    _sealRow, pkgRow⟩ := packet
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed centerUnary radiusUnary containmentRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed scheduleUnary observationUnary routeRow
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed containmentUnary routeUnary handoffRow
  exact
    ⟨centerUnary, radiusUnary, scheduleUnary, observationUnary, containmentUnary, routeUnary,
      handoffUnary, containmentRow, routeRow, handoffRow, pkgRow⟩

theorem DyadicBallPacket_classifier_transport [AskSetup] [PackageSetup]
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
  exact DyadicBallPacket_classifier_laws

end BEDC.Derived.DyadicBallUp
