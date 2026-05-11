import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicBallPacket [AskSetup] [PackageSetup]
    (center radius schedule observation containment transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory schedule ∧
    UnaryHistory observation ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      Cont center radius containment ∧ Cont schedule observation route ∧
        Cont containment route transport ∧ Cont transport provenance name ∧
          PkgSig bundle name pkg

theorem DyadicBallPacket_classifier_transport [AskSetup] [PackageSetup]
    {center radius schedule observation containment transport route provenance name center' radius'
      schedule' observation' containment' transport' route' provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallPacket center radius schedule observation containment transport route provenance
        name bundle pkg ->
      hsame center center' -> hsame radius radius' -> hsame schedule schedule' ->
        hsame observation observation' -> hsame route route' -> hsame provenance provenance' ->
          Cont center' radius' containment' -> Cont schedule' observation' route' ->
            Cont containment' route' transport' -> Cont transport' provenance' name' ->
              PkgSig bundle name' pkg ->
                DyadicBallPacket center' radius' schedule' observation' containment' transport'
                    route' provenance' name' bundle pkg ∧
                  hsame containment containment' ∧ hsame transport transport' ∧ hsame name name' := by
  intro packet sameCenter sameRadius sameSchedule sameObservation sameRoute sameProvenance
    containmentCont' routeCont' transportCont' nameCont' pkgSig'
  obtain ⟨centerUnary, radiusUnary, scheduleUnary, observationUnary, routeUnary,
    provenanceUnary, containmentCont, routeCont, transportCont, nameCont, _pkgSig⟩ := packet
  have centerUnary' : UnaryHistory center' :=
    unary_transport centerUnary sameCenter
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary sameObservation
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have sameContainment : hsame containment containment' :=
    cont_respects_hsame sameCenter sameRadius containmentCont containmentCont'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameContainment sameRoute transportCont transportCont'
  have sameName : hsame name name' :=
    cont_respects_hsame sameTransport sameProvenance nameCont nameCont'
  have transported :
      DyadicBallPacket center' radius' schedule' observation' containment' transport' route'
        provenance' name' bundle pkg :=
    ⟨centerUnary', radiusUnary', scheduleUnary', observationUnary', routeUnary', provenanceUnary',
      containmentCont', routeCont', transportCont', nameCont', pkgSig'⟩
  exact ⟨transported, sameContainment, sameTransport, sameName⟩

end BEDC.Derived.DyadicBallUp
