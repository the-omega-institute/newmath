import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NestedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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
