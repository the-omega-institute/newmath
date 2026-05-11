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

end BEDC.Derived.NestedIntervalUp
