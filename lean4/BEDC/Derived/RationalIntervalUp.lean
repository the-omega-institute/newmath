import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalIntervalPacket [AskSetup] [PackageSetup]
    (left right order containment transport route provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory order ∧ UnaryHistory containment ∧
    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory name ∧ UnaryHistory endpoint ∧ Cont left right order ∧
        Cont order containment transport ∧ Cont transport route provenance ∧
          Cont provenance name endpoint ∧ PkgSig bundle endpoint pkg

theorem RationalIntervalPacket_endpoint_containment_transport [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint left' right' order'
      containment' transport' route' provenance' name' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          hsame containment containment' ->
            hsame route route' ->
              hsame name name' ->
                Cont left' right' order' ->
                  Cont order' containment' transport' ->
                    Cont transport' route' provenance' ->
                      Cont provenance' name' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          RationalIntervalPacket left' right' order' containment' transport'
                              route' provenance' name' endpoint' bundle pkg ∧
                            hsame order order' ∧ hsame transport transport' ∧
                              hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro packet sameLeft sameRight sameContainment sameRoute sameName leftRightOrder'
    orderContainmentTransport' transportRouteProvenance' provenanceNameEndpoint' endpointPkg'
  rcases packet with
    ⟨leftUnary, rightUnary, orderUnary, containmentUnary, transportUnary, routeUnary,
      provenanceUnary, nameUnary, endpointUnary, leftRightOrder, orderContainmentTransport,
      transportRouteProvenance, provenanceNameEndpoint, _endpointPkg⟩
  have sameOrder : hsame order order' :=
    cont_respects_hsame sameLeft sameRight leftRightOrder leftRightOrder'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameOrder sameContainment orderContainmentTransport
      orderContainmentTransport'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameRoute transportRouteProvenance
      transportRouteProvenance'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameName provenanceNameEndpoint provenanceNameEndpoint'
  have leftUnary' : UnaryHistory left' := unary_transport leftUnary sameLeft
  have rightUnary' : UnaryHistory right' := unary_transport rightUnary sameRight
  have orderUnary' : UnaryHistory order' := unary_transport orderUnary sameOrder
  have containmentUnary' : UnaryHistory containment' :=
    unary_transport containmentUnary sameContainment
  have transportUnary' : UnaryHistory transport' := unary_transport transportUnary sameTransport
  have routeUnary' : UnaryHistory route' := unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' := unary_transport nameUnary sameName
  have endpointUnary' : UnaryHistory endpoint' := unary_transport endpointUnary sameEndpoint
  exact
    ⟨⟨leftUnary', rightUnary', orderUnary', containmentUnary', transportUnary', routeUnary',
        provenanceUnary', nameUnary', endpointUnary', leftRightOrder',
        orderContainmentTransport', transportRouteProvenance', provenanceNameEndpoint',
        endpointPkg'⟩,
      sameOrder, sameTransport, sameProvenance, sameEndpoint⟩

theorem RationalIntervalPacket_realup_consumer_exactness [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont endpoint containment consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory order ∧
            UnaryHistory containment ∧ UnaryHistory endpoint ∧ UnaryHistory consumer ∧
              Cont left right order ∧ Cont endpoint containment consumer ∧
                PkgSig bundle consumer pkg := by
  intro packet endpointContainmentConsumer consumerPkg
  rcases packet with
    ⟨leftUnary, rightUnary, orderUnary, containmentUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _nameUnary, endpointUnary, leftRightOrder, _orderContainmentTransport,
      _transportRouteProvenance, _provenanceNameEndpoint, _endpointPkg⟩
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary containmentUnary endpointContainmentConsumer
  exact
    ⟨leftUnary, rightUnary, orderUnary, containmentUnary, endpointUnary, consumerUnary,
      leftRightOrder, endpointContainmentConsumer, consumerPkg⟩

end BEDC.Derived.RationalIntervalUp
