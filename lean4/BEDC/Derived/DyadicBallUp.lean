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
