import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalUp

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

theorem NestedIntervalFiniteCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
        endpoint pkgLedger bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
              endpoint pkgLedger bundle pkg ∧
            (hsame row endpoint ∨ hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
              endpoint pkgLedger bundle pkg ∧
            (hsame row endpoint ∨ hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
              endpoint pkgLedger bundle pkg ∧
            (hsame row endpoint ∨ hsame row pkgLedger))
        hsame := by
  intro carrier
  have sourceAtEndpoint :
      NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
          endpoint pkgLedger bundle pkg ∧
        (hsame endpoint endpoint ∨ hsame endpoint pkgLedger) :=
    ⟨carrier, Or.inl (hsame_refl endpoint)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
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
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl sameEndpoint =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint)
        | inr sameLedger =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameLedger)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem NestedIntervalPacket_window_refinement [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger extra lower'
      upper' order' width' inclusion' schedule' regRead' sealFace' endpoint' pkgLedger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace endpoint
        pkgLedger bundle pkg ->
      UnaryHistory extra ->
        Cont lower extra lower' ->
          Cont upper extra upper' ->
            Cont order extra order' ->
              Cont width extra width' ->
                Cont inclusion extra inclusion' ->
                  Cont schedule extra schedule' ->
                    Cont regRead extra regRead' ->
                      Cont sealFace extra sealFace' ->
                        Cont lower' upper' endpoint' ->
                          Cont endpoint' order' pkgLedger' ->
                            PkgSig bundle pkgLedger' pkg ->
                              NestedIntervalFiniteCarrier lower' upper' order' width' inclusion'
                                schedule' regRead' sealFace' endpoint' pkgLedger' bundle pkg := by
  intro carrier extraUnary lowerRow upperRow orderRow widthRow inclusionRow scheduleRow regReadRow
    sealFaceRow endpointRow ledgerRow pkgRow
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
                                  have lowerUnary' : UnaryHistory lower' :=
                                    unary_cont_closed lowerUnary extraUnary lowerRow
                                  have upperUnary' : UnaryHistory upper' :=
                                    unary_cont_closed upperUnary extraUnary upperRow
                                  have orderUnary' : UnaryHistory order' :=
                                    unary_cont_closed orderUnary extraUnary orderRow
                                  have widthUnary' : UnaryHistory width' :=
                                    unary_cont_closed widthUnary extraUnary widthRow
                                  have inclusionUnary' : UnaryHistory inclusion' :=
                                    unary_cont_closed inclusionUnary extraUnary inclusionRow
                                  have scheduleUnary' : UnaryHistory schedule' :=
                                    unary_cont_closed scheduleUnary extraUnary scheduleRow
                                  have regReadUnary' : UnaryHistory regRead' :=
                                    unary_cont_closed regReadUnary extraUnary regReadRow
                                  have sealFaceUnary' : UnaryHistory sealFace' :=
                                    unary_cont_closed sealFaceUnary extraUnary sealFaceRow
                                  have endpointUnary' : UnaryHistory endpoint' :=
                                    unary_cont_closed lowerUnary' upperUnary' endpointRow
                                  have pkgLedgerUnary' : UnaryHistory pkgLedger' :=
                                    unary_cont_closed endpointUnary' orderUnary' ledgerRow
                                  exact
                                    ⟨lowerUnary', upperUnary', orderUnary', widthUnary',
                                      inclusionUnary', scheduleUnary', regReadUnary',
                                      sealFaceUnary', endpointUnary', pkgLedgerUnary',
                                      endpointRow, ledgerRow, pkgRow⟩

theorem NestedIntervalFiniteCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace endpoint
        pkgLedger bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
              endpoint pkgLedger bundle pkg ∧
            (hsame row endpoint ∨ hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
              endpoint pkgLedger bundle pkg ∧
            (hsame row endpoint ∨ hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
              endpoint pkgLedger bundle pkg ∧
            (hsame row endpoint ∨ hsame row pkgLedger))
        hsame := by
  intro carrier
  let Surface : BHist -> Prop :=
    fun row : BHist =>
      NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
          endpoint pkgLedger bundle pkg ∧
        (hsame row endpoint ∨ hsame row pkgLedger)
  have endpointSource : Surface endpoint :=
    And.intro carrier (Or.inl (hsame_refl endpoint))
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        cases sourceRow.right with
        | inl endpointRow =>
            exact And.intro sourceRow.left
              (Or.inl (hsame_trans (hsame_symm same) endpointRow))
        | inr ledgerRow =>
            exact And.intro sourceRow.left
              (Or.inr (hsame_trans (hsame_symm same) ledgerRow))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

def NestedIntervalRegSeqRatWindow [AskSetup] [PackageSetup]
    (unaryPrefix lower upper width inclusion schedule regRead provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory unaryPrefix ∧ UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory width ∧
    UnaryHistory inclusion ∧ UnaryHistory schedule ∧ UnaryHistory regRead ∧
      UnaryHistory provenance ∧ UnaryHistory cert ∧ Cont lower upper width ∧
        Cont width inclusion regRead ∧ PkgSig bundle regRead pkg

theorem NestedIntervalRegSeqRatWindow_handoff [AskSetup] [PackageSetup]
    {unaryPrefix lower upper width inclusion schedule regRead provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalRegSeqRatWindow unaryPrefix lower upper width inclusion schedule regRead
        provenance cert bundle pkg ->
      UnaryHistory unaryPrefix ∧ UnaryHistory lower ∧ UnaryHistory upper ∧
        UnaryHistory width ∧ UnaryHistory inclusion ∧ UnaryHistory schedule ∧
          UnaryHistory regRead ∧ Cont lower upper width ∧ Cont width inclusion regRead ∧
            PkgSig bundle regRead pkg := by
  intro window
  obtain ⟨prefixUnary, lowerUnary, upperUnary, widthUnary, inclusionUnary, scheduleUnary,
    regReadUnary, _provenanceUnary, _certUnary, lowerUpperRow, widthInclusionRow,
    pkgRow⟩ := window
  have prefixHistory : UnaryHistory unaryPrefix := prefixUnary
  have lowerHistory : UnaryHistory lower := lowerUnary
  have upperHistory : UnaryHistory upper := upperUnary
  have widthHistory : UnaryHistory width := widthUnary
  have inclusionHistory : UnaryHistory inclusion := inclusionUnary
  have scheduleHistory : UnaryHistory schedule := scheduleUnary
  have regReadHistory : UnaryHistory regRead := regReadUnary
  have lowerUpper : Cont lower upper width := lowerUpperRow
  have widthInclusion : Cont width inclusion regRead := widthInclusionRow
  have regReadPkg : PkgSig bundle regRead pkg := pkgRow
  exact
    ⟨prefixHistory, lowerHistory, upperHistory, widthHistory, inclusionHistory, scheduleHistory,
      regReadHistory, lowerUpper, widthInclusion, regReadPkg⟩

theorem NestedIntervalFiniteCarrier_consumer_bridge_boundary [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger provenance
      cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace endpoint
        pkgLedger bundle pkg ->
      NestedIntervalRegSeqRatWindow schedule lower upper width inclusion schedule regRead provenance
        cert bundle pkg ->
        hsame order inclusion ->
          hsame endpoint width ∧ hsame pkgLedger regRead ∧ PkgSig bundle regRead pkg := by
  intro carrier window sameOrderInclusion
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _widthUnary, _inclusionUnary, _scheduleUnary,
    _regReadUnary, _sealFaceUnary, _endpointUnary, _pkgLedgerUnary, endpointRow, ledgerRow,
    _carrierPkg⟩ := carrier
  obtain ⟨_scheduleUnaryWindow, _lowerUnaryWindow, _upperUnaryWindow, _widthUnaryWindow,
    _inclusionUnaryWindow, _scheduleUnaryWindow', _regReadUnaryWindow, _provenanceUnary,
    _certUnary, lowerUpperWidthRow, widthInclusionRow, regReadPkg⟩ := window
  have sameEndpointWidth : hsame endpoint width :=
    cont_respects_hsame (hsame_refl lower) (hsame_refl upper) endpointRow lowerUpperWidthRow
  have sameLedgerRegRead : hsame pkgLedger regRead :=
    cont_respects_hsame sameEndpointWidth sameOrderInclusion ledgerRow widthInclusionRow
  exact ⟨sameEndpointWidth, sameLedgerRegRead, regReadPkg⟩

theorem NestedIntervalPacket_consumer_bridge_finite_route_exactness [AskSetup] [PackageSetup]
    {unaryPrefix lower upper width inclusion schedule regRead provenance cert bridgeRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalRegSeqRatWindow unaryPrefix lower upper width inclusion schedule regRead
        provenance cert bundle pkg ->
      Cont regRead cert bridgeRoute ->
        PkgSig bundle bridgeRoute pkg ->
          UnaryHistory bridgeRoute ∧ hsame width (append lower upper) ∧
            hsame regRead (append width inclusion) ∧ Cont regRead cert bridgeRoute ∧
              PkgSig bundle bridgeRoute pkg := by
  intro window bridgeRouteRow bridgePkg
  obtain ⟨_prefixUnary, _lowerUnary, _upperUnary, _widthUnary, _inclusionUnary, _scheduleUnary,
    regReadUnary, _provenanceUnary, certUnary, lowerUpperRow, widthInclusionRow,
    _regReadPkg⟩ := window
  have bridgeUnary : UnaryHistory bridgeRoute :=
    unary_cont_closed regReadUnary certUnary bridgeRouteRow
  exact
    ⟨bridgeUnary, lowerUpperRow, widthInclusionRow, bridgeRouteRow, bridgePkg⟩

theorem NestedIntervalFiniteCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
        endpoint pkgLedger bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
            endpoint pkgLedger bundle pkg ∧
            (hsame row sealFace ∨ hsame row regRead ∨ hsame row endpoint ∨
              hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
            endpoint pkgLedger bundle pkg ∧
            (hsame row sealFace ∨ hsame row regRead ∨ hsame row endpoint ∨
              hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
            endpoint pkgLedger bundle pkg ∧
            (hsame row sealFace ∨ hsame row regRead ∨ hsame row endpoint ∨
              hsame row pkgLedger))
        hsame := by
  intro carrier
  let SealSurface : BHist -> Prop :=
    fun row : BHist =>
      NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
        endpoint pkgLedger bundle pkg ∧
        (hsame row sealFace ∨ hsame row regRead ∨ hsame row endpoint ∨ hsame row pkgLedger)
  have sealSource : SealSurface sealFace :=
    And.intro carrier (Or.inl (hsame_refl sealFace))
  have transportSurface :
      forall {row row' : BHist}, hsame row row' -> SealSurface row -> SealSurface row' := by
    intro row row' sameRow sourceRow
    have rowFromRow' : hsame row' row :=
      hsame_symm sameRow
    cases sourceRow.right with
    | inl sameSeal =>
        exact And.intro sourceRow.left (Or.inl (hsame_trans rowFromRow' sameSeal))
    | inr rest =>
        cases rest with
        | inl sameRegRead =>
            exact And.intro sourceRow.left (Or.inr (Or.inl (hsame_trans rowFromRow' sameRegRead)))
        | inr rest' =>
            cases rest' with
            | inl sameEndpoint =>
                exact
                  And.intro sourceRow.left
                    (Or.inr (Or.inr (Or.inl (hsame_trans rowFromRow' sameEndpoint))))
            | inr samePkgLedger =>
                exact
                  And.intro sourceRow.left
                    (Or.inr (Or.inr (Or.inr (hsame_trans rowFromRow' samePkgLedger))))
  exact {
    core := {
      carrier_inhabited := Exists.intro sealFace sealSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact transportSurface same sourceRow
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem NestedIntervalFiniteCarrier_public_window_boundary [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace endpoint
        pkgLedger bundle pkg ->
      NestedIntervalRegSeqRatWindow schedule lower upper width inclusion schedule regRead pkgLedger
        endpoint bundle pkg ->
        UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory width ∧
          UnaryHistory inclusion ∧ UnaryHistory schedule ∧ UnaryHistory regRead ∧
            UnaryHistory sealFace ∧ Cont lower upper endpoint ∧ Cont lower upper width ∧
              Cont width inclusion regRead ∧ PkgSig bundle pkgLedger pkg ∧
                PkgSig bundle regRead pkg := by
  intro carrier window
  obtain ⟨lowerUnary, upperUnary, _orderUnary, widthUnary, inclusionUnary, scheduleUnary,
    regReadUnary, sealFaceUnary, _endpointUnary, _pkgLedgerUnary, endpointRow, _ledgerRow,
    ledgerPkg⟩ := carrier
  obtain ⟨_prefixUnary, _windowLowerUnary, _windowUpperUnary, _windowWidthUnary,
    _windowInclusionUnary, _windowScheduleUnary, _windowRegReadUnary, _provenanceUnary,
    _certUnary, widthRow, regReadRow, regReadPkg⟩ := window
  exact
    ⟨lowerUnary, upperUnary, widthUnary, inclusionUnary, scheduleUnary, regReadUnary,
      sealFaceUnary, endpointRow, widthRow, regReadRow, ledgerPkg, regReadPkg⟩

end BEDC.Derived.NestedIntervalUp

namespace BEDC.Derived

structure NestedIntervalTheoremUp where
  nestedWindow : BEDC.Derived.NestedIntervalUp.NestedIntervalUp
  dyadicLedger : BHist
  streamWindow : BHist
  regularReadback : BHist
  realSeal : BHist

end BEDC.Derived
