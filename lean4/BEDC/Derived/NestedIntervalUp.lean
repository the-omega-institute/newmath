import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalUp : Type where
  | mk :
      (interval endpoint width schedule regular sealRow transportRow provenance cert : BHist) →
        NestedIntervalUp
  deriving DecidableEq

def nestedIntervalEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalEncodeBHist h

def nestedIntervalDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalDecodeBHist tail)

def nestedIntervalToEventFlow : NestedIntervalUp → EventFlow
  | NestedIntervalUp.mk interval endpoint width schedule regular sealRow transportRow provenance
      cert =>
      [[BMark.b0], nestedIntervalEncodeBHist interval,
        [BMark.b1, BMark.b0], nestedIntervalEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b0], nestedIntervalEncodeBHist width,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], nestedIntervalEncodeBHist schedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          nestedIntervalEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          nestedIntervalEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          nestedIntervalEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
          nestedIntervalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
          nestedIntervalEncodeBHist cert]

def nestedIntervalFromEventFlow : EventFlow → Option NestedIntervalUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | interval :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | endpoint :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | width :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | schedule :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | regular :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | sealRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transportRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | cert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (NestedIntervalUp.mk
                                                                                  (nestedIntervalDecodeBHist
                                                                                    interval)
                                                                                  (nestedIntervalDecodeBHist
                                                                                    endpoint)
                                                                                  (nestedIntervalDecodeBHist
                                                                                    width)
                                                                                  (nestedIntervalDecodeBHist
                                                                                    schedule)
                                                                                  (nestedIntervalDecodeBHist
                                                                                    regular)
                                                                                  (nestedIntervalDecodeBHist
                                                                                    sealRow)
                                                                                  (nestedIntervalDecodeBHist
                                                                                    transportRow)
                                                                                  (nestedIntervalDecodeBHist
                                                                                    provenance)
                                                                                  (nestedIntervalDecodeBHist
                                                                                    cert))
                                                                          | _ :: _ => none

instance nestedIntervalBHistCarrier : BHistCarrier NestedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalToEventFlow
  fromEventFlow := nestedIntervalFromEventFlow

instance nestedIntervalChapterTasteGate : ChapterTasteGate NestedIntervalUp where
  round_trip := by
    intro x
    have decodeEncode :
        ∀ h : BHist, nestedIntervalDecodeBHist (nestedIntervalEncodeBHist h) = h := by
      intro h
      induction h with
      | Empty => rfl
      | e0 h ih =>
          exact congrArg BHist.e0 ih
      | e1 h ih =>
          exact congrArg BHist.e1 ih
    cases x with
    | mk interval endpoint width schedule regular sealRow transportRow provenance cert =>
        change
          some (NestedIntervalUp.mk
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist interval))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist endpoint))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist width))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist schedule))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist regular))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist sealRow))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist transportRow))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist provenance))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist cert))) =
            some
              (NestedIntervalUp.mk interval endpoint width schedule regular sealRow transportRow
                provenance cert)
        rw [decodeEncode interval, decodeEncode endpoint, decodeEncode width,
          decodeEncode schedule, decodeEncode regular, decodeEncode sealRow,
          decodeEncode transportRow, decodeEncode provenance, decodeEncode cert]
  layer_separation := by
    intro x y hxy heq
    apply hxy
    have decodeEncode :
        ∀ h : BHist, nestedIntervalDecodeBHist (nestedIntervalEncodeBHist h) = h := by
      intro h
      induction h with
      | Empty => rfl
      | e0 h ih =>
          exact congrArg BHist.e0 ih
      | e1 h ih =>
          exact congrArg BHist.e1 ih
    have roundTrip :
        ∀ x : NestedIntervalUp,
          nestedIntervalFromEventFlow (nestedIntervalToEventFlow x) = some x := by
      intro x
      cases x with
      | mk interval endpoint width schedule regular sealRow transportRow provenance cert =>
          change
            some (NestedIntervalUp.mk
              (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist interval))
              (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist endpoint))
              (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist width))
              (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist schedule))
              (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist regular))
              (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist sealRow))
              (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist transportRow))
              (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist provenance))
              (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist cert))) =
              some
                (NestedIntervalUp.mk interval endpoint width schedule regular sealRow transportRow
                  provenance cert)
          rw [decodeEncode interval, decodeEncode endpoint, decodeEncode width,
            decodeEncode schedule, decodeEncode regular, decodeEncode sealRow,
            decodeEncode transportRow, decodeEncode provenance, decodeEncode cert]
    have hread :
        nestedIntervalFromEventFlow (nestedIntervalToEventFlow x) =
          nestedIntervalFromEventFlow (nestedIntervalToEventFlow y) :=
      congrArg nestedIntervalFromEventFlow heq
    exact Option.some.inj (Eq.trans (roundTrip x).symm (Eq.trans hread (roundTrip y)))

theorem NestedIntervalTasteGate_single_carrier_alignment :
    (forall h : BHist, nestedIntervalDecodeBHist (nestedIntervalEncodeBHist h) = h) /\
      (forall x : NestedIntervalUp,
        nestedIntervalFromEventFlow (BHistCarrier.toEventFlow x) = some x) /\
      (forall x y : NestedIntervalUp,
        BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y) /\
      nestedIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  have decodeEncode :
      ∀ h : BHist, nestedIntervalDecodeBHist (nestedIntervalEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have roundTrip :
      ∀ x : NestedIntervalUp,
        nestedIntervalFromEventFlow (BHistCarrier.toEventFlow x) = some x := by
    intro x
    change nestedIntervalFromEventFlow (nestedIntervalToEventFlow x) = some x
    cases x with
    | mk interval endpoint width schedule regular sealRow transportRow provenance cert =>
        change
          some (NestedIntervalUp.mk
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist interval))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist endpoint))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist width))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist schedule))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist regular))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist sealRow))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist transportRow))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist provenance))
            (nestedIntervalDecodeBHist (nestedIntervalEncodeBHist cert))) =
            some
              (NestedIntervalUp.mk interval endpoint width schedule regular sealRow transportRow
                provenance cert)
        rw [decodeEncode interval, decodeEncode endpoint, decodeEncode width,
          decodeEncode schedule, decodeEncode regular, decodeEncode sealRow,
          decodeEncode transportRow, decodeEncode provenance, decodeEncode cert]
  have injective :
      ∀ x y : NestedIntervalUp,
        BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y := by
    intro x y heq
    change nestedIntervalToEventFlow x = nestedIntervalToEventFlow y at heq
    have hread :
        nestedIntervalFromEventFlow (nestedIntervalToEventFlow x) =
          nestedIntervalFromEventFlow (nestedIntervalToEventFlow y) :=
      congrArg nestedIntervalFromEventFlow heq
    have leftRead : nestedIntervalFromEventFlow (nestedIntervalToEventFlow x) = some x := by
      exact roundTrip x
    have rightRead : nestedIntervalFromEventFlow (nestedIntervalToEventFlow y) = some y := by
      exact roundTrip y
    exact Option.some.inj (Eq.trans leftRead.symm (Eq.trans hread rightRead))
  exact ⟨decodeEncode, roundTrip, injective, rfl⟩

def NestedIntervalFinitePacket [AskSetup] [PackageSetup]
    (interval endpoint width schedule regular sealRow transportRow provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory interval ∧ UnaryHistory endpoint ∧ UnaryHistory width ∧
    UnaryHistory schedule ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
      UnaryHistory transportRow ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont interval endpoint width ∧ Cont width schedule regular ∧
          Cont regular sealRow transportRow ∧ Cont transportRow provenance cert ∧
            PkgSig bundle cert pkg

theorem NestedIntervalFinitePacket_endpoint_transport [AskSetup] [PackageSetup]
    {interval endpoint width schedule regular sealRow transportRow provenance cert interval'
      endpoint' width' schedule' regular' sealRow' transportRow' provenance' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFinitePacket interval endpoint width schedule regular sealRow transportRow
        provenance cert bundle pkg ->
      hsame interval interval' ->
        hsame endpoint endpoint' ->
          hsame schedule schedule' ->
            hsame sealRow sealRow' ->
              hsame provenance provenance' ->
                Cont interval' endpoint' width' ->
                  Cont width' schedule' regular' ->
                    Cont regular' sealRow' transportRow' ->
                      Cont transportRow' provenance' cert' ->
                        PkgSig bundle cert' pkg ->
                          NestedIntervalFinitePacket interval' endpoint' width' schedule' regular'
                              sealRow' transportRow' provenance' cert' bundle pkg ∧
                            hsame width width' ∧ hsame regular regular' ∧ hsame cert cert' := by
  intro packet sameInterval sameEndpoint sameSchedule sameSealRow sameProvenance
  intro widthRow' regularRow' transportRowRow' certRow' pkgRow'
  obtain ⟨intervalUnary, endpointUnary, _widthUnary, scheduleUnary, _regularUnary,
    sealRowUnary, _transportRowUnary, provenanceUnary, _certUnary, widthRow, regularRow,
    transportRowRow, certRow, _pkgRow⟩ := packet
  have intervalUnary' : UnaryHistory interval' :=
    unary_transport intervalUnary sameInterval
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have sealRowUnary' : UnaryHistory sealRow' :=
    unary_transport sealRowUnary sameSealRow
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have widthUnary' : UnaryHistory width' :=
    unary_cont_closed intervalUnary' endpointUnary' widthRow'
  have regularUnary' : UnaryHistory regular' :=
    unary_cont_closed widthUnary' scheduleUnary' regularRow'
  have transportRowUnary' : UnaryHistory transportRow' :=
    unary_cont_closed regularUnary' sealRowUnary' transportRowRow'
  have certUnary' : UnaryHistory cert' :=
    unary_cont_closed transportRowUnary' provenanceUnary' certRow'
  have sameWidth : hsame width width' :=
    cont_respects_hsame sameInterval sameEndpoint widthRow widthRow'
  have sameRegular : hsame regular regular' :=
    cont_respects_hsame sameWidth sameSchedule regularRow regularRow'
  have sameTransportRow : hsame transportRow transportRow' :=
    cont_respects_hsame sameRegular sameSealRow transportRowRow transportRowRow'
  have sameCert : hsame cert cert' :=
    cont_respects_hsame sameTransportRow sameProvenance certRow certRow'
  constructor
  · exact ⟨intervalUnary', endpointUnary', widthUnary', scheduleUnary', regularUnary',
      sealRowUnary', transportRowUnary', provenanceUnary', certUnary', widthRow', regularRow',
      transportRowRow', certRow', pkgRow'⟩
  · exact ⟨sameWidth, sameRegular, sameCert⟩

def NestedIntervalFiniteCarrier [AskSetup] [PackageSetup]
    (lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧ UnaryHistory width ∧
    UnaryHistory inclusion ∧ UnaryHistory schedule ∧ UnaryHistory regRead ∧
      UnaryHistory sealFace ∧ UnaryHistory endpoint ∧ UnaryHistory pkgLedger ∧
        Cont lower upper endpoint ∧ Cont endpoint order pkgLedger ∧ PkgSig bundle pkgLedger pkg

theorem NestedIntervalFiniteCarrier_endpoint_transport [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger lower' upper'
      order' width' inclusion' schedule' regRead' sealFace' endpoint' pkgLedger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace endpoint
        pkgLedger bundle pkg ->
      hsame lower lower' ->
        hsame upper upper' ->
          hsame order order' ->
            hsame width width' ->
              hsame inclusion inclusion' ->
                hsame schedule schedule' ->
                  hsame regRead regRead' ->
                    hsame sealFace sealFace' ->
                      Cont lower' upper' endpoint' ->
                        Cont endpoint' order' pkgLedger' ->
                          PkgSig bundle pkgLedger' pkg ->
                            NestedIntervalFiniteCarrier lower' upper' order' width' inclusion'
                                schedule' regRead' sealFace' endpoint' pkgLedger' bundle pkg ∧
                              hsame endpoint endpoint' ∧ hsame pkgLedger pkgLedger' := by
  intro carrier sameLower sameUpper sameOrder sameWidth sameInclusion sameSchedule sameRegRead
    sameSealFace endpointRow' ledgerRow' pkgRow'
  cases carrier with
  | intro lowerUnary rest =>
      cases rest with
      | intro upperUnary rest =>
          cases rest with
          | intro orderUnary rest =>
              cases rest with
              | intro widthUnary rest =>
                  cases rest with
                  | intro inclusionUnary rest =>
                      cases rest with
                      | intro scheduleUnary rest =>
                          cases rest with
                          | intro regReadUnary rest =>
                              cases rest with
                              | intro sealFaceUnary rest =>
                                  cases rest with
                                  | intro _endpointUnary rest =>
                                      cases rest with
                                      | intro _pkgLedgerUnary rest =>
                                          cases rest with
                                          | intro endpointRow rest =>
                                              cases rest with
                                              | intro ledgerRow _pkgRow =>
                                                  have lowerUnary' : UnaryHistory lower' :=
                                                    unary_transport lowerUnary sameLower
                                                  have upperUnary' : UnaryHistory upper' :=
                                                    unary_transport upperUnary sameUpper
                                                  have orderUnary' : UnaryHistory order' :=
                                                    unary_transport orderUnary sameOrder
                                                  have widthUnary' : UnaryHistory width' :=
                                                    unary_transport widthUnary sameWidth
                                                  have inclusionUnary' : UnaryHistory inclusion' :=
                                                    unary_transport inclusionUnary sameInclusion
                                                  have scheduleUnary' : UnaryHistory schedule' :=
                                                    unary_transport scheduleUnary sameSchedule
                                                  have regReadUnary' : UnaryHistory regRead' :=
                                                    unary_transport regReadUnary sameRegRead
                                                  have sealFaceUnary' : UnaryHistory sealFace' :=
                                                    unary_transport sealFaceUnary sameSealFace
                                                  have endpointUnary' : UnaryHistory endpoint' :=
                                                    unary_cont_closed lowerUnary' upperUnary'
                                                      endpointRow'
                                                  have pkgLedgerUnary' : UnaryHistory pkgLedger' :=
                                                    unary_cont_closed endpointUnary' orderUnary'
                                                      ledgerRow'
                                                  have sameEndpoint : hsame endpoint endpoint' :=
                                                    cont_respects_hsame sameLower sameUpper
                                                      endpointRow endpointRow'
                                                  have sameLedger : hsame pkgLedger pkgLedger' :=
                                                    cont_respects_hsame sameEndpoint sameOrder
                                                      ledgerRow ledgerRow'
                                                  exact
                                                    ⟨⟨lowerUnary', upperUnary', orderUnary',
                                                      widthUnary', inclusionUnary',
                                                      scheduleUnary', regReadUnary',
                                                      sealFaceUnary', endpointUnary',
                                                      pkgLedgerUnary', endpointRow', ledgerRow',
                                                      pkgRow'⟩, sameEndpoint, sameLedger⟩

end BEDC.Derived.NestedIntervalUp
