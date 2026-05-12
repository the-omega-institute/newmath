import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalBallPacket [AskSetup] [PackageSetup]
    (center radius order transport containment provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory order ∧
    UnaryHistory transport ∧ UnaryHistory containment ∧ UnaryHistory provenance ∧
      UnaryHistory name ∧ Cont center radius order ∧ Cont order containment transport ∧
        Cont transport provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem RationalBallPacket_refinement_transport [AskSetup] [PackageSetup]
    {center radius order transport containment provenance name endpoint center' radius' order'
      transport' containment' provenance' name' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalBallPacket center radius order transport containment provenance name endpoint
        bundle pkg ->
      hsame center center' ->
        hsame radius radius' ->
          hsame containment containment' ->
            hsame provenance provenance' ->
              hsame name name' ->
                Cont center' radius' order' ->
                  Cont order' containment' transport' ->
                    Cont transport' provenance' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        RationalBallPacket center' radius' order' transport' containment'
                            provenance' name' endpoint' bundle pkg ∧
                          hsame order order' ∧ hsame transport transport' ∧
                            hsame endpoint endpoint' := by
  intro packet sameCenter sameRadius sameContainment sameProvenance sameName
    centerRadiusOrder' orderContainmentTransport' transportProvenanceEndpoint' endpointPkg'
  rcases packet with
    ⟨centerUnary, radiusUnary, orderUnary, transportUnary, containmentUnary,
      provenanceUnary, nameUnary, centerRadiusOrder, orderContainmentTransport,
      transportProvenanceEndpoint, _endpointPkg⟩
  have sameOrder : hsame order order' :=
    cont_respects_hsame sameCenter sameRadius centerRadiusOrder centerRadiusOrder'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameOrder sameContainment orderContainmentTransport
      orderContainmentTransport'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameTransport sameProvenance transportProvenanceEndpoint
      transportProvenanceEndpoint'
  have centerUnary' : UnaryHistory center' := unary_transport centerUnary sameCenter
  have radiusUnary' : UnaryHistory radius' := unary_transport radiusUnary sameRadius
  have orderUnary' : UnaryHistory order' := unary_transport orderUnary sameOrder
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have containmentUnary' : UnaryHistory containment' :=
    unary_transport containmentUnary sameContainment
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' := unary_transport nameUnary sameName
  exact
    ⟨⟨centerUnary', radiusUnary', orderUnary', transportUnary', containmentUnary',
        provenanceUnary', nameUnary', centerRadiusOrder', orderContainmentTransport',
        transportProvenanceEndpoint', endpointPkg'⟩,
      sameOrder, sameTransport, sameEndpoint⟩

theorem RationalBallPacket_realup_window_handoff [AskSetup] [PackageSetup]
    {center radius order transport containment provenance name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalBallPacket center radius order transport containment provenance name endpoint
        bundle pkg ->
      Cont containment endpoint consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory order ∧
            UnaryHistory containment ∧ UnaryHistory endpoint ∧ UnaryHistory consumer ∧
              Cont center radius order ∧ Cont order containment transport ∧
                Cont transport provenance endpoint ∧ Cont containment endpoint consumer ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle consumer pkg := by
  intro packet consumerRow consumerPkg
  obtain ⟨centerUnary, radiusUnary, orderUnary, transportUnary, containmentUnary,
    provenanceUnary, _nameUnary, centerRadiusOrder, orderContainmentTransport,
    transportProvenanceEndpoint, endpointPkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary provenanceUnary transportProvenanceEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed containmentUnary endpointUnary consumerRow
  exact
    ⟨centerUnary, radiusUnary, orderUnary, containmentUnary, endpointUnary, consumerUnary,
      centerRadiusOrder, orderContainmentTransport, transportProvenanceEndpoint, consumerRow,
      endpointPkg, consumerPkg⟩

end BEDC.Derived.RationalBallUp
