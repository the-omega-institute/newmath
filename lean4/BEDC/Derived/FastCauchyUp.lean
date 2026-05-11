import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastCauchyUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastCauchyUp : Type where
  | mk :
      (stream modulus endpoint latePair transport window provenance nameRow : BHist) →
        FastCauchyUp
  deriving DecidableEq

def fastCauchyEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastCauchyEncodeBHist h

def fastCauchyDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastCauchyDecodeBHist tail)

def fastCauchyToEventFlow : FastCauchyUp → EventFlow
  | FastCauchyUp.mk stream modulus endpoint latePair transport window provenance nameRow =>
      [[BMark.b0], fastCauchyEncodeBHist stream,
        [BMark.b1, BMark.b0], fastCauchyEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0], fastCauchyEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], fastCauchyEncodeBHist latePair,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          fastCauchyEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          fastCauchyEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          fastCauchyEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
          fastCauchyEncodeBHist nameRow]

def fastCauchyFromEventFlow : EventFlow → Option FastCauchyUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | stream :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | endpoint :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | latePair :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | window :: rest11 =>
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
                                                              | nameRow :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (FastCauchyUp.mk
                                                                          (fastCauchyDecodeBHist
                                                                            stream)
                                                                          (fastCauchyDecodeBHist
                                                                            modulus)
                                                                          (fastCauchyDecodeBHist
                                                                            endpoint)
                                                                          (fastCauchyDecodeBHist
                                                                            latePair)
                                                                          (fastCauchyDecodeBHist
                                                                            transport)
                                                                          (fastCauchyDecodeBHist
                                                                            window)
                                                                          (fastCauchyDecodeBHist
                                                                            provenance)
                                                                          (fastCauchyDecodeBHist
                                                                            nameRow))
                                                                  | _ :: _ => none

instance fastCauchyBHistCarrier : BHistCarrier FastCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastCauchyToEventFlow
  fromEventFlow := fastCauchyFromEventFlow

instance fastCauchyChapterTasteGate : ChapterTasteGate FastCauchyUp where
  round_trip := by
    intro x
    have decodeEncode :
        ∀ h : BHist, fastCauchyDecodeBHist (fastCauchyEncodeBHist h) = h := by
      intro h
      induction h with
      | Empty => rfl
      | e0 h ih =>
          exact congrArg BHist.e0 ih
      | e1 h ih =>
          exact congrArg BHist.e1 ih
    cases x with
    | mk stream modulus endpoint latePair transport window provenance nameRow =>
        change
          some (FastCauchyUp.mk
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist stream))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist modulus))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist endpoint))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist latePair))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist transport))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist window))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist provenance))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist nameRow))) =
            some
              (FastCauchyUp.mk stream modulus endpoint latePair transport window provenance
                nameRow)
        rw [decodeEncode stream, decodeEncode modulus, decodeEncode endpoint,
          decodeEncode latePair, decodeEncode transport, decodeEncode window,
          decodeEncode provenance, decodeEncode nameRow]
  layer_separation := by
    intro x y hxy heq
    apply hxy
    have decodeEncode :
        ∀ h : BHist, fastCauchyDecodeBHist (fastCauchyEncodeBHist h) = h := by
      intro h
      induction h with
      | Empty => rfl
      | e0 h ih =>
          exact congrArg BHist.e0 ih
      | e1 h ih =>
          exact congrArg BHist.e1 ih
    have roundTrip :
        ∀ x : FastCauchyUp, fastCauchyFromEventFlow (fastCauchyToEventFlow x) = some x := by
      intro x
      cases x with
      | mk stream modulus endpoint latePair transport window provenance nameRow =>
          change
            some (FastCauchyUp.mk
              (fastCauchyDecodeBHist (fastCauchyEncodeBHist stream))
              (fastCauchyDecodeBHist (fastCauchyEncodeBHist modulus))
              (fastCauchyDecodeBHist (fastCauchyEncodeBHist endpoint))
              (fastCauchyDecodeBHist (fastCauchyEncodeBHist latePair))
              (fastCauchyDecodeBHist (fastCauchyEncodeBHist transport))
              (fastCauchyDecodeBHist (fastCauchyEncodeBHist window))
              (fastCauchyDecodeBHist (fastCauchyEncodeBHist provenance))
              (fastCauchyDecodeBHist (fastCauchyEncodeBHist nameRow))) =
              some
                (FastCauchyUp.mk stream modulus endpoint latePair transport window provenance
                  nameRow)
          rw [decodeEncode stream, decodeEncode modulus, decodeEncode endpoint,
            decodeEncode latePair, decodeEncode transport, decodeEncode window,
            decodeEncode provenance, decodeEncode nameRow]
    have hread :
        fastCauchyFromEventFlow (fastCauchyToEventFlow x) =
          fastCauchyFromEventFlow (fastCauchyToEventFlow y) :=
      congrArg fastCauchyFromEventFlow heq
    exact Option.some.inj (Eq.trans (roundTrip x).symm (Eq.trans hread (roundTrip y)))

theorem FastCauchyTasteGate_single_carrier_alignment :
    (forall h : BHist, fastCauchyDecodeBHist (fastCauchyEncodeBHist h) = h) /\
      (forall x : FastCauchyUp,
        fastCauchyFromEventFlow (BHistCarrier.toEventFlow x) = some x) /\
      (forall x y : FastCauchyUp,
        BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y) /\
      fastCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  have decodeEncode :
      ∀ h : BHist, fastCauchyDecodeBHist (fastCauchyEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have roundTrip :
      ∀ x : FastCauchyUp, fastCauchyFromEventFlow (BHistCarrier.toEventFlow x) = some x := by
    intro x
    change fastCauchyFromEventFlow (fastCauchyToEventFlow x) = some x
    cases x with
    | mk stream modulus endpoint latePair transport window provenance nameRow =>
        change
          some (FastCauchyUp.mk
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist stream))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist modulus))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist endpoint))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist latePair))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist transport))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist window))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist provenance))
            (fastCauchyDecodeBHist (fastCauchyEncodeBHist nameRow))) =
            some
              (FastCauchyUp.mk stream modulus endpoint latePair transport window provenance
                nameRow)
        rw [decodeEncode stream, decodeEncode modulus, decodeEncode endpoint,
          decodeEncode latePair, decodeEncode transport, decodeEncode window,
          decodeEncode provenance, decodeEncode nameRow]
  have injective :
      ∀ x y : FastCauchyUp, BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y := by
    intro x y heq
    change fastCauchyToEventFlow x = fastCauchyToEventFlow y at heq
    have hread :
        fastCauchyFromEventFlow (fastCauchyToEventFlow x) =
          fastCauchyFromEventFlow (fastCauchyToEventFlow y) :=
      congrArg fastCauchyFromEventFlow heq
    have leftRead : fastCauchyFromEventFlow (fastCauchyToEventFlow x) = some x := by
      exact roundTrip x
    have rightRead : fastCauchyFromEventFlow (fastCauchyToEventFlow y) = some y := by
      exact roundTrip y
    exact Option.some.inj (Eq.trans leftRead.symm (Eq.trans hread rightRead))
  exact ⟨decodeEncode, roundTrip, injective, rfl⟩

def FastCauchyPacket [AskSetup] [PackageSetup]
    (stream modulus endpoint latePair transport window provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
    UnaryHistory latePair ∧ UnaryHistory transport ∧ UnaryHistory window ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont stream modulus endpoint ∧
        Cont endpoint latePair window ∧ Cont window transport provenance ∧
          PkgSig bundle provenance pkg

theorem FastCauchyPacket_modulus_transport [AskSetup] [PackageSetup]
    {stream modulus endpoint latePair transport window provenance nameRow stream' modulus'
      endpoint' latePair' transport' window' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
        bundle pkg ->
      hsame stream stream' ->
        hsame modulus modulus' ->
          hsame latePair latePair' ->
            hsame transport transport' ->
              hsame nameRow nameRow' ->
                Cont stream' modulus' endpoint' ->
                  Cont endpoint' latePair' window' ->
                    Cont window' transport' provenance' ->
                      PkgSig bundle provenance' pkg ->
                        FastCauchyPacket stream' modulus' endpoint' latePair' transport'
                            window' provenance' nameRow' bundle pkg ∧
                          hsame endpoint endpoint' ∧ hsame window window' ∧
                            hsame provenance provenance' := by
  intro packet sameStream sameModulus sameLatePair sameTransport sameNameRow
    targetEndpoint targetWindow targetProvenance targetPkg
  have streamUnary : UnaryHistory stream :=
    packet.left
  have modulusUnary : UnaryHistory modulus :=
    packet.right.left
  have latePairUnary : UnaryHistory latePair :=
    packet.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    packet.right.right.right.right.left
  have nameRowUnary : UnaryHistory nameRow :=
    packet.right.right.right.right.right.right.right.left
  have sourceEndpoint : Cont stream modulus endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have sourceWindow : Cont endpoint latePair window :=
    packet.right.right.right.right.right.right.right.right.right.left
  have sourceProvenance : Cont window transport provenance :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have streamUnary' : UnaryHistory stream' :=
    unary_transport streamUnary sameStream
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed streamUnary' modulusUnary' targetEndpoint
  have latePairUnary' : UnaryHistory latePair' :=
    unary_transport latePairUnary sameLatePair
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed endpointUnary' latePairUnary' targetWindow
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed windowUnary' transportUnary' targetProvenance
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_transport nameRowUnary sameNameRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameStream sameModulus sourceEndpoint targetEndpoint
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameEndpoint sameLatePair sourceWindow targetWindow
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameWindow sameTransport sourceProvenance targetProvenance
  exact
    ⟨⟨streamUnary', modulusUnary', endpointUnary', latePairUnary', transportUnary',
        windowUnary', provenanceUnary', nameRowUnary', targetEndpoint, targetWindow,
        targetProvenance, targetPkg⟩,
      sameEndpoint, sameWindow, sameProvenance⟩

def FastCauchyRegSeqRatWindow [AskSetup] [PackageSetup]
    (stream modulus endpoint radius latePair transportWindow regWindow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    UnaryHistory latePair ∧ UnaryHistory transportWindow ∧ UnaryHistory regWindow ∧
      Cont stream modulus transportWindow ∧ Cont endpoint radius latePair ∧
        Cont latePair transportWindow regWindow ∧ PkgSig bundle regWindow pkg

def FastCauchyFinitePacket [AskSetup] [PackageSetup]
    (stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    UnaryHistory latePair ∧ UnaryHistory transportWindow ∧ UnaryHistory regWindow ∧
      UnaryHistory sealBoundary ∧ UnaryHistory certRow ∧ Cont stream modulus transportWindow ∧
        Cont endpoint radius latePair ∧ Cont latePair transportWindow regWindow ∧
          Cont regWindow sealBoundary certRow ∧ PkgSig bundle regWindow pkg

theorem FastCauchyFinitePacket_regseqrat_handoff [AskSetup] [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      FastCauchyRegSeqRatWindow stream modulus endpoint radius latePair transportWindow
          regWindow bundle pkg ∧
        Cont stream modulus transportWindow ∧ Cont endpoint radius latePair ∧
          Cont latePair transportWindow regWindow ∧ PkgSig bundle regWindow pkg := by
  intro packet
  obtain ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, latePairUnary,
    transportUnary, regUnary, _sealUnary, _certUnary, streamModulusRoute,
    endpointRadiusRoute, latePairTransportRoute, _certRoute, pkgRow⟩ := packet
  exact
    ⟨⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, latePairUnary, transportUnary,
        regUnary, streamModulusRoute, endpointRadiusRoute, latePairTransportRoute, pkgRow⟩,
      streamModulusRoute, endpointRadiusRoute, latePairTransportRoute, pkgRow⟩

end BEDC.Derived.FastCauchyUp
