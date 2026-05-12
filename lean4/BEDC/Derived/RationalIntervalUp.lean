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

theorem RationalIntervalRefinement_composition {left mid right lm lmr mr lmr' : BHist} :
    Cont left mid lm -> Cont lm right lmr -> Cont mid right mr -> Cont left mr lmr' ->
      hsame lmr lmr' := by
  intro leftMid leftMidRight midRight leftMidRight'
  exact cont_assoc_hsame leftMid leftMidRight midRight leftMidRight'

theorem RationalIntervalEndpointRows_order_witness [AskSetup] [PackageSetup]
    {left right order left' right' order' endpointPair endpointPair' orderSurface
      orderSurface' provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory left ->
      UnaryHistory right ->
        UnaryHistory order ->
          Cont left right endpointPair ->
            Cont endpointPair order orderSurface ->
              PkgSig bundle provenance pkg ->
                hsame left left' ->
                  hsame right right' ->
                    hsame order order' ->
                      Cont left' right' endpointPair' ->
                        Cont endpointPair' order' orderSurface' ->
                          PkgSig bundle provenance pkg ->
                            UnaryHistory left' ∧ UnaryHistory right' ∧
                              UnaryHistory order' ∧ hsame endpointPair endpointPair' ∧
                                hsame orderSurface orderSurface' ∧
                                  Cont left' right' endpointPair' ∧
                                    Cont endpointPair' order' orderSurface' ∧
                                      PkgSig bundle provenance pkg := by
  intro leftUnary rightUnary orderUnary endpointRow orderRow _pkgSig sameLeft sameRight sameOrder
    endpointRow' orderRow' pkgSig'
  have leftUnary' : UnaryHistory left' :=
    unary_transport leftUnary sameLeft
  have rightUnary' : UnaryHistory right' :=
    unary_transport rightUnary sameRight
  have orderUnary' : UnaryHistory order' :=
    unary_transport orderUnary sameOrder
  have sameEndpointPair : hsame endpointPair endpointPair' :=
    cont_respects_hsame sameLeft sameRight endpointRow endpointRow'
  have sameOrderSurface : hsame orderSurface orderSurface' :=
    cont_respects_hsame sameEndpointPair sameOrder orderRow orderRow'
  exact
    ⟨leftUnary', rightUnary', orderUnary', sameEndpointPair, sameOrderSurface, endpointRow',
      orderRow', pkgSig'⟩

theorem RationalIntervalFiniteConsumer_completeness [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint bridge consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory bridge ->
        Cont endpoint bridge consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory order ∧
              UnaryHistory containment ∧ UnaryHistory endpoint ∧ UnaryHistory bridge ∧
                UnaryHistory consumer ∧ Cont left right order ∧
                  Cont order containment transport ∧ Cont transport route provenance ∧
                    Cont provenance name endpoint ∧ Cont endpoint bridge consumer ∧
                      PkgSig bundle consumer pkg := by
  intro packet bridgeUnary endpointBridgeConsumer consumerPkg
  obtain ⟨leftUnary, rightUnary, orderUnary, containmentUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, endpointUnary, leftRightOrder, orderContainmentTransport,
    transportRouteProvenance, provenanceNameEndpoint, _endpointPkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary bridgeUnary endpointBridgeConsumer
  exact
    ⟨leftUnary, rightUnary, orderUnary, containmentUnary, endpointUnary, bridgeUnary,
      consumerUnary, leftRightOrder, orderContainmentTransport, transportRouteProvenance,
      provenanceNameEndpoint, endpointBridgeConsumer, consumerPkg⟩

end BEDC.Derived.RationalIntervalUp
