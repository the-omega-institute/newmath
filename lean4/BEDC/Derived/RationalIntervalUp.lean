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

theorem RationalIntervalPacket_refinement_composition [AskSetup] [PackageSetup]
    {left middle right orderA orderB containmentA containmentB transportA transportB routeA
      routeB provenanceA provenanceB nameA nameB endpointA endpointB outerOrder outerTransport
      outerProvenance outerEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left middle orderA containmentA transportA routeA provenanceA nameA
        endpointA bundle pkg ->
      RationalIntervalPacket middle right orderB containmentB transportB routeB provenanceB nameB
        endpointB bundle pkg ->
        hsame left middle ->
          hsame containmentA containmentB ->
            hsame routeA routeB ->
              hsame nameA nameB ->
                Cont left right outerOrder ->
                  Cont outerOrder containmentA outerTransport ->
                    Cont outerTransport routeA outerProvenance ->
                      Cont outerProvenance nameA outerEndpoint ->
                        PkgSig bundle outerEndpoint pkg ->
                          RationalIntervalPacket left right outerOrder containmentA outerTransport
                              routeA outerProvenance nameA outerEndpoint bundle pkg ∧
                            hsame outerOrder orderB ∧ hsame outerTransport transportB ∧
                              hsame outerProvenance provenanceB ∧ hsame outerEndpoint endpointB := by
  intro leftPacket rightPacket sameLeftMiddle sameContainment sameRoute sameName outerOrderRow
    outerTransportRow outerProvenanceRow outerEndpointRow outerPkg
  rcases leftPacket with
    ⟨leftUnary, _middleUnaryA, _orderUnaryA, containmentUnary, _transportUnaryA, routeUnary,
      _provenanceUnaryA, nameUnary, _endpointUnaryA, _leftMiddleOrderA,
      _orderContainmentTransportA, _transportRouteProvenanceA, _provenanceNameEndpointA,
      _endpointPkgA⟩
  rcases rightPacket with
    ⟨_middleUnaryB, rightUnary, _orderUnaryB, _containmentUnaryB, _transportUnaryB,
      _routeUnaryB, _provenanceUnaryB, _nameUnaryB, _endpointUnaryB, middleRightOrderB,
      orderContainmentTransportB, transportRouteProvenanceB, provenanceNameEndpointB,
      _endpointPkgB⟩
  have sameOuterOrder : hsame outerOrder orderB :=
    cont_respects_hsame sameLeftMiddle (hsame_refl right) outerOrderRow middleRightOrderB
  have sameOuterTransport : hsame outerTransport transportB :=
    cont_respects_hsame sameOuterOrder sameContainment outerTransportRow
      orderContainmentTransportB
  have sameOuterProvenance : hsame outerProvenance provenanceB :=
    cont_respects_hsame sameOuterTransport sameRoute outerProvenanceRow
      transportRouteProvenanceB
  have sameOuterEndpoint : hsame outerEndpoint endpointB :=
    cont_respects_hsame sameOuterProvenance sameName outerEndpointRow provenanceNameEndpointB
  have outerOrderUnary : UnaryHistory outerOrder :=
    unary_cont_closed leftUnary rightUnary outerOrderRow
  have outerTransportUnary : UnaryHistory outerTransport :=
    unary_cont_closed outerOrderUnary containmentUnary outerTransportRow
  have outerProvenanceUnary : UnaryHistory outerProvenance :=
    unary_cont_closed outerTransportUnary routeUnary outerProvenanceRow
  have outerEndpointUnary : UnaryHistory outerEndpoint :=
    unary_cont_closed outerProvenanceUnary nameUnary outerEndpointRow
  exact
    ⟨⟨leftUnary, rightUnary, outerOrderUnary, containmentUnary, outerTransportUnary,
        routeUnary, outerProvenanceUnary, nameUnary, outerEndpointUnary, outerOrderRow,
        outerTransportRow, outerProvenanceRow, outerEndpointRow, outerPkg⟩,
      sameOuterOrder, sameOuterTransport, sameOuterProvenance, sameOuterEndpoint⟩

end BEDC.Derived.RationalIntervalUp
