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

theorem RationalIntervalPacket_endpoint_order_classifier [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint left' right' order' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          Cont left' right' order' ->
            UnaryHistory left' ∧ UnaryHistory right' ∧ UnaryHistory order' ∧
              Cont left' right' order' ∧ hsame order order' := by
  intro packet sameLeft sameRight leftRightOrder'
  rcases packet with
    ⟨leftUnary, rightUnary, orderUnary, _containmentUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _nameUnary, _endpointUnary, leftRightOrder, _orderContainmentTransport,
      _transportRouteProvenance, _provenanceNameEndpoint, _endpointPkg⟩
  have sameOrder : hsame order order' :=
    cont_respects_hsame sameLeft sameRight leftRightOrder leftRightOrder'
  exact
    ⟨unary_transport leftUnary sameLeft, unary_transport rightUnary sameRight,
      unary_transport orderUnary sameOrder, leftRightOrder', sameOrder⟩

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

theorem RationalIntervalPacket_window_consumer_exhaustion [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint consumer readback :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory consumer ->
        Cont endpoint consumer readback ->
          PkgSig bundle readback pkg ->
            UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory order ∧
              UnaryHistory containment ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                UnaryHistory provenance ∧ UnaryHistory name ∧ UnaryHistory endpoint ∧
                  UnaryHistory readback ∧ Cont left right order ∧
                    Cont order containment transport ∧ Cont transport route provenance ∧
                      Cont provenance name endpoint ∧ Cont endpoint consumer readback ∧
                        PkgSig bundle readback pkg := by
  intro packet consumerUnary consumerReadbackRow readbackPkg
  obtain ⟨leftUnary, rightUnary, orderUnary, containmentUnary, transportUnary, routeUnary,
    provenanceUnary, nameUnary, endpointUnary, leftRightRow, containmentRow, routeRow,
    endpointRow, _endpointPkg⟩ := packet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed endpointUnary consumerUnary consumerReadbackRow
  exact
    ⟨leftUnary, rightUnary, orderUnary, containmentUnary, transportUnary, routeUnary,
      provenanceUnary, nameUnary, endpointUnary, readbackUnary, leftRightRow, containmentRow,
      routeRow, endpointRow, consumerReadbackRow, readbackPkg⟩

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

theorem RationalIntervalPacket_endpoint_order_transport [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint left' right' order' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          Cont left' right' order' ->
            UnaryHistory left' ∧ UnaryHistory right' ∧ UnaryHistory order' ∧
              hsame order order' ∧ Cont left' right' order' := by
  intro packet sameLeft sameRight leftRightOrder'
  rcases packet with
    ⟨leftUnary, rightUnary, orderUnary, _containmentUnary, _transportUnary, _routeUnary,
      _provenanceUnary, _nameUnary, _endpointUnary, leftRightOrder, _orderContainmentTransport,
      _transportRouteProvenance, _provenanceNameEndpoint, _endpointPkg⟩
  have sameOrder : hsame order order' :=
    cont_respects_hsame sameLeft sameRight leftRightOrder leftRightOrder'
  exact
    ⟨unary_transport leftUnary sameLeft, unary_transport rightUnary sameRight,
      unary_transport orderUnary sameOrder, sameOrder, leftRightOrder'⟩

theorem RationalIntervalPacket_common_refinement_window [AskSetup] [PackageSetup]
    {left1 right1 order1 containment1 transport1 route1 provenance1 name1 endpoint1 left2
      right2 order2 containment2 transport2 route2 provenance2 name2 endpoint2 left right order
      containment transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left1 right1 order1 containment1 transport1 route1 provenance1 name1
        endpoint1 bundle pkg ->
      RationalIntervalPacket left2 right2 order2 containment2 transport2 route2 provenance2 name2
          endpoint2 bundle pkg ->
        hsame left1 left ->
          hsame right1 right ->
            hsame containment1 containment ->
              hsame route1 route ->
                hsame name1 name ->
                  hsame left2 left ->
                    hsame right2 right ->
                      hsame containment2 containment ->
                        hsame route2 route ->
                          hsame name2 name ->
                            Cont left right order ->
                              Cont order containment transport ->
                                Cont transport route provenance ->
                                  Cont provenance name endpoint ->
                                    PkgSig bundle endpoint pkg ->
                                      RationalIntervalPacket left right order containment transport
                                          route provenance name endpoint bundle pkg ∧
                                        hsame order1 order ∧ hsame order2 order ∧
                                          hsame transport1 transport ∧
                                            hsame transport2 transport ∧
                                              hsame provenance1 provenance ∧
                                                hsame provenance2 provenance ∧
                                                  hsame endpoint1 endpoint ∧
                                                    hsame endpoint2 endpoint := by
  intro packet1 packet2 sameLeft1 sameRight1 sameContainment1 sameRoute1 sameName1 sameLeft2
    sameRight2 sameContainment2 sameRoute2 sameName2 leftRightOrder orderContainmentTransport
    transportRouteProvenance provenanceNameEndpoint endpointPkg
  have firstTransport :=
    RationalIntervalPacket_endpoint_containment_transport packet1 sameLeft1 sameRight1
      sameContainment1 sameRoute1 sameName1 leftRightOrder orderContainmentTransport
      transportRouteProvenance provenanceNameEndpoint endpointPkg
  have secondTransport :=
    RationalIntervalPacket_endpoint_containment_transport packet2 sameLeft2 sameRight2
      sameContainment2 sameRoute2 sameName2 leftRightOrder orderContainmentTransport
      transportRouteProvenance provenanceNameEndpoint endpointPkg
  exact
    ⟨firstTransport.left,
      firstTransport.right.left,
      secondTransport.right.left,
      firstTransport.right.right.left,
      secondTransport.right.right.left,
      firstTransport.right.right.right.left,
      secondTransport.right.right.right.left,
      firstTransport.right.right.right.right,
      secondTransport.right.right.right.right⟩

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

theorem RationalIntervalPacket_endpoint_width_ledger [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint width : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont left right width ->
        UnaryHistory width ∧ hsame width order ∧ UnaryHistory containment ∧
          Cont order containment transport ∧ PkgSig bundle endpoint pkg := by
  intro packet widthRow
  obtain ⟨leftUnary, rightUnary, _orderUnary, containmentUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, orderRow, containmentRow,
    _provenanceRow, _endpointRow, endpointPkg⟩ := packet
  have widthUnary : UnaryHistory width :=
    unary_cont_closed leftUnary rightUnary widthRow
  have sameWidthOrder : hsame width order :=
    cont_deterministic widthRow orderRow
  exact ⟨widthUnary, sameWidthOrder, containmentUnary, containmentRow, endpointPkg⟩

theorem RationalIntervalPacket_containment_ledger_exactness [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont containment route read ->
        UnaryHistory containment ∧ UnaryHistory route ∧ UnaryHistory read ∧
          Cont containment route read ∧ PkgSig bundle endpoint pkg := by
  intro packet containmentRouteRead
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, containmentUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, _leftRightOrder, _orderContainmentTransport,
    _transportRouteProvenance, _provenanceNameEndpoint, endpointPkg⟩ := packet
  have readUnary : UnaryHistory read :=
    unary_cont_closed containmentUnary routeUnary containmentRouteRead
  exact ⟨containmentUnary, routeUnary, readUnary, containmentRouteRead, endpointPkg⟩

end BEDC.Derived.RationalIntervalUp
