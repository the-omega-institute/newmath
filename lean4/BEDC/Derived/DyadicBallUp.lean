import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

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

inductive DyadicBallUp : Type where
  | mk :
      (center radius schedule observation containment route provenance endpoint : BHist) →
        DyadicBallUp
  deriving DecidableEq

def dyadicBallEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicBallEncodeBHist h

def dyadicBallDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicBallDecodeBHist tail)

def dyadicBallToEventFlow : DyadicBallUp → EventFlow
  | DyadicBallUp.mk center radius schedule observation containment route provenance endpoint =>
      [[BMark.b0], dyadicBallEncodeBHist center,
        [BMark.b1, BMark.b0], dyadicBallEncodeBHist radius,
        [BMark.b1, BMark.b1, BMark.b0], dyadicBallEncodeBHist schedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], dyadicBallEncodeBHist observation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          dyadicBallEncodeBHist containment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          dyadicBallEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          dyadicBallEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
          dyadicBallEncodeBHist endpoint]

def dyadicBallFromEventFlow : EventFlow → Option DyadicBallUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | center :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | radius :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | schedule :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | observation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | containment :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | endpoint :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (DyadicBallUp.mk
                                                                          (dyadicBallDecodeBHist
                                                                            center)
                                                                          (dyadicBallDecodeBHist
                                                                            radius)
                                                                          (dyadicBallDecodeBHist
                                                                            schedule)
                                                                          (dyadicBallDecodeBHist
                                                                            observation)
                                                                          (dyadicBallDecodeBHist
                                                                            containment)
                                                                          (dyadicBallDecodeBHist
                                                                            route)
                                                                          (dyadicBallDecodeBHist
                                                                            provenance)
                                                                          (dyadicBallDecodeBHist
                                                                            endpoint))
                                                                  | _ :: _ => none

instance dyadicBallBHistCarrier : BHistCarrier DyadicBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicBallToEventFlow
  fromEventFlow := dyadicBallFromEventFlow

instance dyadicBallChapterTasteGate : ChapterTasteGate DyadicBallUp where
  round_trip := by
    intro x
    have decodeEncode :
        ∀ h : BHist, dyadicBallDecodeBHist (dyadicBallEncodeBHist h) = h := by
      intro h
      induction h with
      | Empty => rfl
      | e0 h ih =>
          exact congrArg BHist.e0 ih
      | e1 h ih =>
          exact congrArg BHist.e1 ih
    cases x with
    | mk center radius schedule observation containment route provenance endpoint =>
        change
          some (DyadicBallUp.mk
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist center))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist radius))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist schedule))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist observation))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist containment))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist route))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist provenance))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist endpoint))) =
            some
              (DyadicBallUp.mk center radius schedule observation containment route provenance
                endpoint)
        rw [decodeEncode center, decodeEncode radius, decodeEncode schedule,
          decodeEncode observation, decodeEncode containment, decodeEncode route,
          decodeEncode provenance, decodeEncode endpoint]
  layer_separation := by
    intro x y hxy heq
    apply hxy
    have decodeEncode :
        ∀ h : BHist, dyadicBallDecodeBHist (dyadicBallEncodeBHist h) = h := by
      intro h
      induction h with
      | Empty => rfl
      | e0 h ih =>
          exact congrArg BHist.e0 ih
      | e1 h ih =>
          exact congrArg BHist.e1 ih
    have roundTrip :
        ∀ x : DyadicBallUp, dyadicBallFromEventFlow (dyadicBallToEventFlow x) = some x := by
      intro x
      cases x with
      | mk center radius schedule observation containment route provenance endpoint =>
          change
            some (DyadicBallUp.mk
              (dyadicBallDecodeBHist (dyadicBallEncodeBHist center))
              (dyadicBallDecodeBHist (dyadicBallEncodeBHist radius))
              (dyadicBallDecodeBHist (dyadicBallEncodeBHist schedule))
              (dyadicBallDecodeBHist (dyadicBallEncodeBHist observation))
              (dyadicBallDecodeBHist (dyadicBallEncodeBHist containment))
              (dyadicBallDecodeBHist (dyadicBallEncodeBHist route))
              (dyadicBallDecodeBHist (dyadicBallEncodeBHist provenance))
              (dyadicBallDecodeBHist (dyadicBallEncodeBHist endpoint))) =
              some
                (DyadicBallUp.mk center radius schedule observation containment route provenance
                  endpoint)
          rw [decodeEncode center, decodeEncode radius, decodeEncode schedule,
            decodeEncode observation, decodeEncode containment, decodeEncode route,
            decodeEncode provenance, decodeEncode endpoint]
    have hread :
        dyadicBallFromEventFlow (dyadicBallToEventFlow x) =
          dyadicBallFromEventFlow (dyadicBallToEventFlow y) :=
      congrArg dyadicBallFromEventFlow heq
    exact Option.some.inj (Eq.trans (roundTrip x).symm (Eq.trans hread (roundTrip y)))

theorem DyadicBallTasteGate_single_carrier_alignment :
    (forall h : BHist, dyadicBallDecodeBHist (dyadicBallEncodeBHist h) = h) /\
      (forall x : DyadicBallUp,
        dyadicBallFromEventFlow (BHistCarrier.toEventFlow x) = some x) /\
      (forall x y : DyadicBallUp,
        BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y) /\
      dyadicBallEncodeBHist BHist.Empty = ([] : List BMark) := by
  have decodeEncode :
      ∀ h : BHist, dyadicBallDecodeBHist (dyadicBallEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have roundTrip :
      ∀ x : DyadicBallUp, dyadicBallFromEventFlow (BHistCarrier.toEventFlow x) = some x := by
    intro x
    change dyadicBallFromEventFlow (dyadicBallToEventFlow x) = some x
    cases x with
    | mk center radius schedule observation containment route provenance endpoint =>
        change
          some (DyadicBallUp.mk
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist center))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist radius))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist schedule))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist observation))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist containment))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist route))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist provenance))
            (dyadicBallDecodeBHist (dyadicBallEncodeBHist endpoint))) =
            some
              (DyadicBallUp.mk center radius schedule observation containment route provenance
                endpoint)
        rw [decodeEncode center, decodeEncode radius, decodeEncode schedule,
          decodeEncode observation, decodeEncode containment, decodeEncode route,
          decodeEncode provenance, decodeEncode endpoint]
  have injective :
      ∀ x y : DyadicBallUp, BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y := by
    intro x y heq
    change dyadicBallToEventFlow x = dyadicBallToEventFlow y at heq
    have hread :
        dyadicBallFromEventFlow (dyadicBallToEventFlow x) =
          dyadicBallFromEventFlow (dyadicBallToEventFlow y) :=
      congrArg dyadicBallFromEventFlow heq
    have leftRead : dyadicBallFromEventFlow (dyadicBallToEventFlow x) = some x := by
      exact roundTrip x
    have rightRead : dyadicBallFromEventFlow (dyadicBallToEventFlow y) = some y := by
      exact roundTrip y
    exact Option.some.inj (Eq.trans leftRead.symm (Eq.trans hread rightRead))
  exact ⟨decodeEncode, roundTrip, injective, rfl⟩

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
