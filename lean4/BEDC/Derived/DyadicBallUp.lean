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

def DyadicBallFiniteCarrier [AskSetup] [PackageSetup]
    (center radius schedule observation containment route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory schedule ∧
    UnaryHistory observation ∧ UnaryHistory containment ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont center radius containment ∧
        Cont schedule observation route ∧ Cont route provenance nameRow ∧
          PkgSig bundle nameRow pkg

theorem DyadicBallFiniteCarrier_radius_refinement_closure [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance nameRow center' radius'
      schedule' observation' containment' route' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteCarrier center radius schedule observation containment route provenance
        nameRow bundle pkg ->
      UnaryHistory radius' ->
        hsame center center' ->
          hsame schedule schedule' ->
            hsame observation observation' ->
              hsame provenance provenance' ->
                Cont center' radius' containment' ->
                  Cont schedule' observation' route' ->
                    Cont route' provenance' nameRow' ->
                      PkgSig bundle nameRow' pkg ->
                        DyadicBallFiniteCarrier center' radius' schedule' observation'
                            containment' route' provenance' nameRow' bundle pkg ∧
                          hsame route route' ∧ hsame nameRow nameRow' := by
  intro carrier radiusUnary' sameCenter sameSchedule sameObservation sameProvenance
    containmentRow' routeRow' nameRowRoute' pkgRow'
  have centerUnary' : UnaryHistory center' :=
    unary_transport carrier.left sameCenter
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport carrier.right.right.left sameSchedule
  have observationUnary' : UnaryHistory observation' :=
    unary_transport carrier.right.right.right.left sameObservation
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport carrier.right.right.right.right.right.right.left sameProvenance
  have containmentUnary' : UnaryHistory containment' :=
    unary_cont_closed centerUnary' radiusUnary' containmentRow'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed scheduleUnary' observationUnary' routeRow'
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_cont_closed routeUnary' provenanceUnary' nameRowRoute'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameSchedule sameObservation
      carrier.right.right.right.right.right.right.right.right.right.left routeRow'
  have sameNameRow : hsame nameRow nameRow' :=
    cont_respects_hsame sameRoute sameProvenance
      carrier.right.right.right.right.right.right.right.right.right.right.left nameRowRoute'
  exact
    ⟨⟨centerUnary', radiusUnary', scheduleUnary', observationUnary', containmentUnary',
        routeUnary', provenanceUnary', nameRowUnary', containmentRow', routeRow',
        nameRowRoute', pkgRow'⟩,
      sameRoute, sameNameRow⟩
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

theorem DyadicBallFiniteWindowPacket_real_seal_boundary [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance certRow handoff
      sealBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteWindowPacket center radius schedule observation containment route
        provenance certRow handoff sealBoundary bundle pkg →
      UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory schedule ∧
        UnaryHistory observation ∧ UnaryHistory containment ∧ UnaryHistory route ∧
          UnaryHistory handoff ∧ UnaryHistory sealBoundary ∧ UnaryHistory certRow ∧
            Cont handoff sealBoundary certRow ∧ hsame certRow (append handoff sealBoundary) ∧
              PkgSig bundle handoff pkg := by
  intro packet
  obtain ⟨centerUnary, radiusUnary, scheduleUnary, observationUnary, _provenanceUnary,
    certUnary, sealUnary, containmentRow, routeRow, handoffRow, _provenanceRow,
    sealBoundaryRow, pkgRow⟩ := packet
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed centerUnary radiusUnary containmentRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed scheduleUnary observationUnary routeRow
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed containmentUnary routeUnary handoffRow
  exact
    ⟨centerUnary, radiusUnary, scheduleUnary, observationUnary, containmentUnary, routeUnary,
      handoffUnary, sealUnary, certUnary, sealBoundaryRow, sealBoundaryRow, pkgRow⟩

theorem DyadicBallFiniteWindowPacket_real_seal_row_boundary [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance certRow handoff
      sealBoundary row : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteWindowPacket center radius schedule observation containment route
        provenance certRow handoff sealBoundary bundle pkg ->
      (hsame row center ∨ hsame row radius ∨ hsame row schedule ∨ hsame row observation ∨
          hsame row containment ∨ hsame row route ∨ hsame row handoff ∨
            hsame row sealBoundary ∨ hsame row certRow) ->
        UnaryHistory row ∧ PkgSig bundle handoff pkg := by
  intro packet rowVisible
  obtain ⟨centerUnary, radiusUnary, scheduleUnary, observationUnary, _provenanceUnary,
    certUnary, sealUnary, containmentRow, routeRow, handoffRow, _certProvenanceRow,
    _certSealRow, pkgRow⟩ := packet
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed centerUnary radiusUnary containmentRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed scheduleUnary observationUnary routeRow
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed containmentUnary routeUnary handoffRow
  have rowUnary : UnaryHistory row := by
    cases rowVisible with
    | inl sameCenter =>
        exact unary_transport centerUnary (hsame_symm sameCenter)
    | inr rowVisible =>
        cases rowVisible with
        | inl sameRadius =>
            exact unary_transport radiusUnary (hsame_symm sameRadius)
        | inr rowVisible =>
            cases rowVisible with
            | inl sameSchedule =>
                exact unary_transport scheduleUnary (hsame_symm sameSchedule)
            | inr rowVisible =>
                cases rowVisible with
                | inl sameObservation =>
                    exact unary_transport observationUnary (hsame_symm sameObservation)
                | inr rowVisible =>
                    cases rowVisible with
                    | inl sameContainment =>
                        exact unary_transport containmentUnary (hsame_symm sameContainment)
                    | inr rowVisible =>
                        cases rowVisible with
                        | inl sameRoute =>
                            exact unary_transport routeUnary (hsame_symm sameRoute)
                        | inr rowVisible =>
                            cases rowVisible with
                            | inl sameHandoff =>
                                exact unary_transport handoffUnary (hsame_symm sameHandoff)
                            | inr rowVisible =>
                                cases rowVisible with
                                | inl sameSeal =>
                                    exact unary_transport sealUnary (hsame_symm sameSeal)
                                | inr sameCert =>
                                    exact unary_transport certUnary (hsame_symm sameCert)
  exact ⟨rowUnary, pkgRow⟩

theorem DyadicBallFiniteWindowPacket_common_observation_overlap [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance certRow handoff sealBoundary
      center' radius' containment' route' provenance' certRow' handoff' sealBoundary' commonRadius
      commonContainment commonRoute commonHandoff commonCertRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteWindowPacket center radius schedule observation containment route provenance
        certRow handoff sealBoundary bundle pkg ->
      DyadicBallFiniteWindowPacket center' radius' schedule observation containment' route'
          provenance' certRow' handoff' sealBoundary' bundle pkg ->
        UnaryHistory commonRadius -> hsame center center' -> hsame provenance provenance' ->
          hsame sealBoundary sealBoundary' ->
            Cont center commonRadius commonContainment -> Cont schedule observation commonRoute ->
              Cont commonContainment commonRoute commonHandoff ->
                Cont commonHandoff provenance commonCertRow ->
                  Cont commonHandoff sealBoundary commonCertRow ->
                    PkgSig bundle commonHandoff pkg ->
                      forall overlapReads : List BHist,
                        (forall row : BHist, row ∈ overlapReads -> UnaryHistory row) ->
                          UnaryHistory (overlapReads.foldl append commonHandoff) ∧
                            hsame commonHandoff (append commonContainment commonRoute) := by
  intro packet _packet' commonRadiusUnary _sameCenter _sameProvenance _sameSeal
  intro commonContainmentRow commonRouteRow commonHandoffRow _commonCertByProvenance
  intro _commonCertBySeal _commonPackage overlapReads
  obtain ⟨centerUnary, _radiusUnary, scheduleUnary, observationUnary, _provenanceUnary,
    _certUnary, _sealUnary, _containmentRow, _routeRow, _handoffRow, _provenanceRow,
    _sealRow, _pkgRow⟩ := packet
  have commonContainmentUnary : UnaryHistory commonContainment :=
    unary_cont_closed centerUnary commonRadiusUnary commonContainmentRow
  have commonRouteUnary : UnaryHistory commonRoute :=
    unary_cont_closed scheduleUnary observationUnary commonRouteRow
  have commonHandoffUnary : UnaryHistory commonHandoff :=
    unary_cont_closed commonContainmentUnary commonRouteUnary commonHandoffRow
  have overlapClosed :
      (forall row : BHist, row ∈ overlapReads -> UnaryHistory row) ->
        UnaryHistory (overlapReads.foldl append commonHandoff) := by
    have foldClosed :
        forall base : BHist,
          UnaryHistory base ->
            (forall row : BHist, row ∈ overlapReads -> UnaryHistory row) ->
              UnaryHistory (overlapReads.foldl append base) := by
      induction overlapReads with
      | nil =>
          intro base baseUnary _readUnary
          exact baseUnary
      | cons read tail ih =>
          intro base baseUnary readUnary
          have readHeadUnary : UnaryHistory read :=
            readUnary read (List.Mem.head tail)
          have nextHandoffUnary : UnaryHistory (append base read) :=
            unary_append_closed baseUnary readHeadUnary
          exact ih (append base read) nextHandoffUnary
            (fun row rowInTail => readUnary row (List.Mem.tail read rowInTail))
    intro readUnary
    exact foldClosed commonHandoff commonHandoffUnary readUnary
  intro readUnary
  exact ⟨overlapClosed readUnary, commonHandoffRow⟩

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

theorem DyadicBallPacket_regseqrat_window_handoff [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallPacket center radius schedule observation containment route provenance endpoint
        bundle pkg ->
      UnaryHistory schedule ∧ UnaryHistory center ∧ UnaryHistory radius ∧
        UnaryHistory observation ∧ UnaryHistory containment ∧ Cont center radius schedule ∧
          Cont schedule observation containment ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact
    ⟨packet.right.right.left, packet.left, packet.right.left,
      packet.right.right.right.left, packet.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right⟩

theorem DyadicBallFiniteWindowPacket_refinement_overlap_transitivity [AskSetup]
    [PackageSetup]
    {center0 radius0 center1 radius1 center2 radius2 schedule observation containment0
      containment1 containment2 route0 route1 route2 provenance0 provenance1 provenance2 certRow0
      certRow1 certRow2 handoff0 handoff1 handoff2 sealBoundary0 sealBoundary1
      sealBoundary2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteWindowPacket center0 radius0 schedule observation containment0 route0
        provenance0 certRow0 handoff0 sealBoundary0 bundle pkg ->
      DyadicBallFiniteWindowPacket center1 radius1 schedule observation containment1 route1
          provenance1 certRow1 handoff1 sealBoundary1 bundle pkg ->
        DyadicBallFiniteWindowPacket center2 radius2 schedule observation containment2 route2
            provenance2 certRow2 handoff2 sealBoundary2 bundle pkg ->
          hsame center0 center1 ->
            hsame center1 center2 ->
              hsame radius0 radius1 ->
                hsame radius1 radius2 ->
                  hsame provenance0 provenance1 ->
                    hsame provenance1 provenance2 ->
                      hsame handoff0 handoff2 ∧
                        SemanticNameCert
                          (fun row : BHist =>
                            hsame row handoff0 ∨ hsame row handoff1 ∨ hsame row handoff2 ∨
                              hsame row certRow0 ∨ hsame row certRow1 ∨ hsame row certRow2)
                          (fun row : BHist =>
                            hsame row handoff0 ∨ hsame row handoff1 ∨ hsame row handoff2 ∨
                              hsame row certRow0 ∨ hsame row certRow1 ∨ hsame row certRow2)
                          (fun row : BHist =>
                            hsame row handoff0 ∨ hsame row handoff1 ∨ hsame row handoff2 ∨
                              hsame row certRow0 ∨ hsame row certRow1 ∨ hsame row certRow2)
                          hsame := by
  intro packet0 packet1 packet2 sameCenter01 sameCenter12 sameRadius01 sameRadius12
    sameProvenance01 sameProvenance12
  have sameContainment01 : hsame containment0 containment1 :=
    cont_respects_hsame sameCenter01 sameRadius01
      packet0.right.right.right.right.right.right.right.left
      packet1.right.right.right.right.right.right.right.left
  have sameContainment12 : hsame containment1 containment2 :=
    cont_respects_hsame sameCenter12 sameRadius12
      packet1.right.right.right.right.right.right.right.left
      packet2.right.right.right.right.right.right.right.left
  have sameRoute01 : hsame route0 route1 :=
    cont_respects_hsame (hsame_refl schedule) (hsame_refl observation)
      packet0.right.right.right.right.right.right.right.right.left
      packet1.right.right.right.right.right.right.right.right.left
  have sameRoute12 : hsame route1 route2 :=
    cont_respects_hsame (hsame_refl schedule) (hsame_refl observation)
      packet1.right.right.right.right.right.right.right.right.left
      packet2.right.right.right.right.right.right.right.right.left
  have sameHandoff01 : hsame handoff0 handoff1 :=
    cont_respects_hsame sameContainment01 sameRoute01
      packet0.right.right.right.right.right.right.right.right.right.left
      packet1.right.right.right.right.right.right.right.right.right.left
  have sameHandoff12 : hsame handoff1 handoff2 :=
    cont_respects_hsame sameContainment12 sameRoute12
      packet1.right.right.right.right.right.right.right.right.right.left
      packet2.right.right.right.right.right.right.right.right.right.left
  have sameCert01 : hsame certRow0 certRow1 :=
    cont_respects_hsame sameHandoff01 sameProvenance01
      packet0.right.right.right.right.right.right.right.right.right.right.left
      packet1.right.right.right.right.right.right.right.right.right.right.left
  have sameCert12 : hsame certRow1 certRow2 :=
    cont_respects_hsame sameHandoff12 sameProvenance12
      packet1.right.right.right.right.right.right.right.right.right.right.left
      packet2.right.right.right.right.right.right.right.right.right.right.left
  have sameHandoff02 : hsame handoff0 handoff2 :=
    hsame_trans sameHandoff01 sameHandoff12
  have sourceAtHandoff0 :
      hsame handoff0 handoff0 ∨ hsame handoff0 handoff1 ∨ hsame handoff0 handoff2 ∨
        hsame handoff0 certRow0 ∨ hsame handoff0 certRow1 ∨ hsame handoff0 certRow2 :=
    Or.inl (hsame_refl handoff0)
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row handoff0 ∨ hsame row handoff1 ∨ hsame row handoff2 ∨
            hsame row certRow0 ∨ hsame row certRow1 ∨ hsame row certRow2)
        (fun row : BHist =>
          hsame row handoff0 ∨ hsame row handoff1 ∨ hsame row handoff2 ∨
            hsame row certRow0 ∨ hsame row certRow1 ∨ hsame row certRow2)
        (fun row : BHist =>
          hsame row handoff0 ∨ hsame row handoff1 ∨ hsame row handoff2 ∨
            hsame row certRow0 ∨ hsame row certRow1 ∨ hsame row certRow2)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff0 sourceAtHandoff0
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        cases source with
        | inl sameHandoff0 =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameHandoff0)
        | inr rest =>
            cases rest with
            | inl sameHandoff1 =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameHandoff1))
            | inr rest' =>
                cases rest' with
                | inl sameHandoff2 =>
                    exact Or.inr (Or.inr (Or.inl
                      (hsame_trans (hsame_symm sameRows) sameHandoff2)))
                | inr rest'' =>
                    cases rest'' with
                    | inl sameCert0 =>
                        exact Or.inr (Or.inr (Or.inr (Or.inl
                          (hsame_trans (hsame_symm sameRows) sameCert0))))
                    | inr rest''' =>
                        cases rest''' with
                        | inl sameCert1 =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                              (hsame_trans (hsame_symm sameRows) sameCert1)))))
                        | inr sameCert2 =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                              (hsame_trans (hsame_symm sameRows) sameCert2)))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact ⟨sameHandoff02, cert⟩
theorem DyadicBallFiniteWindowPacket_intersection_refinement_handoff [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance certRow handoff
      sealBoundary smallerRadius containment' handoff' certRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteWindowPacket center radius schedule observation containment route
        provenance certRow handoff sealBoundary bundle pkg ->
      UnaryHistory smallerRadius ->
        Cont center smallerRadius containment' ->
          Cont containment' route handoff' ->
            Cont handoff' provenance certRow' ->
              Cont handoff' sealBoundary certRow' ->
                PkgSig bundle handoff' pkg ->
                  DyadicBallFiniteWindowPacket center smallerRadius schedule observation
                      containment' route provenance certRow' handoff' sealBoundary bundle pkg ∧
                    hsame route (append schedule observation) ∧
                      hsame handoff' (append containment' route) := by
  intro packet smallerRadiusUnary containmentRow' handoffRow' provenanceRow' sealRow' pkgRow'
  obtain ⟨centerUnary, _radiusUnary, scheduleUnary, observationUnary, provenanceUnary,
    _certUnary, sealUnary, _containmentRow, routeRow, _handoffRow, _provenanceRow,
    _sealRow, _packetPkg⟩ := packet
  have containmentUnary' : UnaryHistory containment' :=
    unary_cont_closed centerUnary smallerRadiusUnary containmentRow'
  have routeUnary : UnaryHistory route :=
    unary_cont_closed scheduleUnary observationUnary routeRow
  have handoffUnary' : UnaryHistory handoff' :=
    unary_cont_closed containmentUnary' routeUnary handoffRow'
  have certUnary' : UnaryHistory certRow' :=
    unary_cont_closed handoffUnary' provenanceUnary provenanceRow'
  exact
    ⟨⟨centerUnary, smallerRadiusUnary, scheduleUnary, observationUnary, provenanceUnary,
        certUnary', sealUnary, containmentRow', routeRow, handoffRow', provenanceRow',
        sealRow', pkgRow'⟩,
      routeRow, handoffRow'⟩

end BEDC.Derived.DyadicBallUp
