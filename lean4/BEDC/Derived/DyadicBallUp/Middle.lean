import BEDC.Derived.DyadicBallUp.Core

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

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

theorem DyadicBallPacket_real_seal_boundary [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallPacket center radius schedule observation containment route provenance endpoint
        bundle pkg ->
      UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory schedule ∧
        UnaryHistory observation ∧ UnaryHistory containment ∧ UnaryHistory route ∧
          UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont center radius schedule ∧
            Cont schedule observation containment ∧ Cont containment route endpoint ∧
              hsame schedule (append center radius) ∧
                hsame containment (append schedule observation) ∧
                  hsame endpoint (append containment route) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have centerUnary : UnaryHistory center :=
    packet.left
  have radiusUnary : UnaryHistory radius :=
    packet.right.left
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.left
  have observationUnary : UnaryHistory observation :=
    packet.right.right.right.left
  have containmentUnary : UnaryHistory containment :=
    packet.right.right.right.right.left
  have routeUnary : UnaryHistory route :=
    packet.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.right.right.right.right.right.left
  have scheduleRow : Cont center radius schedule :=
    packet.right.right.right.right.right.right.right.right.left
  have containmentRow : Cont schedule observation containment :=
    packet.right.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont containment route endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨centerUnary,
      radiusUnary,
      scheduleUnary,
      observationUnary,
      containmentUnary,
      routeUnary,
      provenanceUnary,
      endpointUnary,
      scheduleRow,
      containmentRow,
      endpointRow,
      scheduleRow,
      containmentRow,
      endpointRow,
      pkgSig⟩

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


end BEDC.Derived.DyadicBallUp
