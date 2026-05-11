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

end BEDC.Derived.NestedIntervalUp
