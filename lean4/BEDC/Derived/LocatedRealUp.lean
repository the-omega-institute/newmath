import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedRealCarrier [AskSetup] [PackageSetup]
    (stream schedule interval location realRow transport provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory schedule ∧ UnaryHistory interval ∧
    UnaryHistory location ∧ UnaryHistory realRow ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont stream schedule interval ∧
        Cont interval location realRow ∧ Cont realRow transport provenance ∧
          Cont provenance schedule endpoint ∧ PkgSig bundle endpoint pkg

theorem LocatedRealCarrier_transport [AskSetup] [PackageSetup]
    {stream stream' schedule schedule' interval interval' location location' realRow realRow'
      transport transport' provenance provenance' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrier stream schedule interval location realRow transport provenance endpoint
        bundle pkg ->
      hsame stream stream' ->
        hsame schedule schedule' ->
          hsame interval interval' ->
            hsame location location' ->
              hsame realRow realRow' ->
                hsame transport transport' ->
                  Cont stream' schedule' interval' ->
                    Cont interval' location' realRow' ->
                      Cont realRow' transport' provenance' ->
                        Cont provenance' schedule' endpoint' ->
                          PkgSig bundle endpoint' pkg ->
                            LocatedRealCarrier stream' schedule' interval' location' realRow'
                                transport' provenance' endpoint' bundle pkg ∧
                              hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameStream sameSchedule sameInterval sameLocation sameRealRow sameTransport
    streamScheduleInterval' intervalLocationRealRow' realRowTransportProvenance'
    provenanceScheduleEndpoint' endpointPkg'
  obtain ⟨streamUnary, scheduleUnary, intervalUnary, locationUnary, realRowUnary,
    transportUnary, _provenanceUnary, _endpointUnary, streamScheduleInterval,
    intervalLocationRealRow, realRowTransportProvenance, provenanceScheduleEndpoint,
    _endpointPkg⟩ := carrier
  have streamUnary' : UnaryHistory stream' :=
    unary_transport streamUnary sameStream
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have intervalUnary' : UnaryHistory interval' :=
    unary_transport intervalUnary sameInterval
  have locationUnary' : UnaryHistory location' :=
    unary_transport locationUnary sameLocation
  have realRowUnary' : UnaryHistory realRow' :=
    unary_transport realRowUnary sameRealRow
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRealRow sameTransport realRowTransportProvenance
      realRowTransportProvenance'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed realRowUnary' transportUnary' realRowTransportProvenance'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameSchedule provenanceScheduleEndpoint
      provenanceScheduleEndpoint'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' scheduleUnary' provenanceScheduleEndpoint'
  exact
    ⟨⟨streamUnary', scheduleUnary', intervalUnary', locationUnary', realRowUnary',
        transportUnary', provenanceUnary', endpointUnary', streamScheduleInterval',
        intervalLocationRealRow', realRowTransportProvenance', provenanceScheduleEndpoint',
        endpointPkg'⟩,
      sameProvenance, sameEndpoint⟩

end BEDC.Derived.LocatedRealUp
