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

theorem RationalIntervalPacket_dyadic_transport_stability [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint left' right' order'
      containment' transport' route' provenance' name' endpoint' width width' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          hsame containment containment' ->
            hsame route route' ->
              hsame name name' ->
                Cont left right width ->
                  Cont left' right' width' ->
                    Cont left' right' order' ->
                      Cont order' containment' transport' ->
                        Cont transport' route' provenance' ->
                          Cont provenance' name' endpoint' ->
                            PkgSig bundle endpoint' pkg ->
                              RationalIntervalPacket left' right' order' containment'
                                  transport' route' provenance' name' endpoint' bundle pkg ∧
                                hsame width width' ∧ hsame order order' ∧
                                  hsame transport transport' ∧ hsame provenance provenance' ∧
                                    hsame endpoint endpoint' := by
  intro packet sameLeft sameRight sameContainment sameRoute sameName leftRightWidth
    leftRightWidth' leftRightOrder' orderContainmentTransport' transportRouteProvenance'
    provenanceNameEndpoint' endpointPkg'
  have packetTransport :=
    RationalIntervalPacket_endpoint_containment_transport packet sameLeft sameRight
      sameContainment sameRoute sameName leftRightOrder' orderContainmentTransport'
      transportRouteProvenance' provenanceNameEndpoint' endpointPkg'
  have sameWidth : hsame width width' :=
    cont_respects_hsame sameLeft sameRight leftRightWidth leftRightWidth'
  exact
    ⟨packetTransport.left, sameWidth, packetTransport.right.left,
      packetTransport.right.right.left, packetTransport.right.right.right.left,
      packetTransport.right.right.right.right⟩

theorem RationalIntervalPacket_public_rational_window_handoff [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint publicHandoff :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont endpoint provenance publicHandoff ->
        PkgSig bundle publicHandoff pkg ->
          UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory order ∧
            UnaryHistory containment ∧ UnaryHistory endpoint ∧ UnaryHistory publicHandoff ∧
              Cont endpoint provenance publicHandoff ∧ PkgSig bundle publicHandoff pkg := by
  intro packet handoffRow handoffPkg
  obtain ⟨leftUnary, rightUnary, orderUnary, containmentUnary, _transportUnary, _routeUnary,
    provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder, _orderContainmentTransport,
    _transportRouteProvenance, _provenanceNameEndpoint, _endpointPkg⟩ := packet
  have handoffUnary : UnaryHistory publicHandoff :=
    unary_cont_closed endpointUnary provenanceUnary handoffRow
  exact
    ⟨leftUnary, rightUnary, orderUnary, containmentUnary, endpointUnary, handoffUnary,
      handoffRow, handoffPkg⟩

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

theorem RationalIntervalPacket_directed_refinement_basis [AskSetup] [PackageSetup]
    {left1 right1 order1 containment1 transport1 route1 provenance1 name1 endpoint1 left2
      right2 order2 containment2 transport2 route2 provenance2 name2 endpoint2 left right order
      containment transport route provenance name endpoint consumer readback : BHist}
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
                                      UnaryHistory consumer ->
                                        Cont endpoint consumer readback ->
                                          PkgSig bundle readback pkg ->
                                            RationalIntervalPacket left right order containment
                                                transport route provenance name endpoint bundle pkg ∧
                                              UnaryHistory readback ∧ hsame endpoint1 endpoint ∧
                                                hsame endpoint2 endpoint ∧
                                                  Cont endpoint consumer readback ∧
                                                    PkgSig bundle readback pkg := by
  intro packet1 packet2 sameLeft1 sameRight1 sameContainment1 sameRoute1 sameName1 sameLeft2
    sameRight2 sameContainment2 sameRoute2 sameName2 leftRightOrder orderContainmentTransport
    transportRouteProvenance provenanceNameEndpoint endpointPkg consumerUnary endpointConsumerReadback
    readbackPkg
  have common :=
    RationalIntervalPacket_common_refinement_window packet1 packet2 sameLeft1 sameRight1
      sameContainment1 sameRoute1 sameName1 sameLeft2 sameRight2 sameContainment2 sameRoute2
      sameName2 leftRightOrder orderContainmentTransport transportRouteProvenance
      provenanceNameEndpoint endpointPkg
  rcases common with
    ⟨commonPacket, _sameOrder1, _sameOrder2, _sameTransport1, _sameTransport2,
      _sameProvenance1, _sameProvenance2, sameEndpoint1, sameEndpoint2⟩
  have endpointUnary : UnaryHistory endpoint :=
    commonPacket.right.right.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed endpointUnary consumerUnary endpointConsumerReadback
  exact
    ⟨commonPacket, readbackUnary, sameEndpoint1, sameEndpoint2, endpointConsumerReadback,
      readbackPkg⟩

theorem RationalIntervalPacket_bisection_refinement_nesting [AskSetup] [PackageSetup]
    {left mid right parentOrder containment transport route provenance name parentEndpoint
      halfOrder halfTransport halfEndpoint nestedConsumer nestedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right parentOrder containment transport route provenance name
        parentEndpoint bundle pkg ->
      UnaryHistory mid ->
        Cont left mid halfOrder ->
          Cont halfOrder containment halfTransport ->
            Cont halfTransport route provenance ->
              Cont provenance name halfEndpoint ->
                PkgSig bundle halfEndpoint pkg ->
                  UnaryHistory nestedConsumer ->
                    Cont halfEndpoint nestedConsumer nestedRead ->
                      PkgSig bundle nestedRead pkg ->
                        RationalIntervalPacket left mid halfOrder containment halfTransport route
                            provenance name halfEndpoint bundle pkg ∧
                          UnaryHistory nestedRead ∧ Cont halfEndpoint nestedConsumer nestedRead ∧
                            PkgSig bundle nestedRead pkg ∧ hsame parentOrder (append left right) ∧
                              hsame halfOrder (append left mid) := by
  intro packet midUnary leftMidHalfOrder halfOrderContainmentHalfTransport
    halfTransportRouteProvenance provenanceNameHalfEndpoint halfEndpointPkg nestedConsumerUnary
    halfEndpointNestedConsumerNestedRead nestedReadPkg
  rcases packet with
    ⟨leftUnary, _rightUnary, _parentOrderUnary, containmentUnary, _transportUnary, routeUnary,
      _provenanceUnary, nameUnary, _parentEndpointUnary, parentOrderRow,
      _orderContainmentTransport, _transportRouteProvenance, _provenanceNameParentEndpoint,
      _parentEndpointPkg⟩
  have halfOrderUnary : UnaryHistory halfOrder :=
    unary_cont_closed leftUnary midUnary leftMidHalfOrder
  have halfTransportUnary : UnaryHistory halfTransport :=
    unary_cont_closed halfOrderUnary containmentUnary halfOrderContainmentHalfTransport
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed halfTransportUnary routeUnary halfTransportRouteProvenance
  have halfEndpointUnary : UnaryHistory halfEndpoint :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameHalfEndpoint
  have nestedReadUnary : UnaryHistory nestedRead :=
    unary_cont_closed halfEndpointUnary nestedConsumerUnary halfEndpointNestedConsumerNestedRead
  exact
    ⟨⟨leftUnary, midUnary, halfOrderUnary, containmentUnary, halfTransportUnary, routeUnary,
        provenanceUnary, nameUnary, halfEndpointUnary, leftMidHalfOrder,
        halfOrderContainmentHalfTransport, halfTransportRouteProvenance,
        provenanceNameHalfEndpoint, halfEndpointPkg⟩,
      nestedReadUnary, halfEndpointNestedConsumerNestedRead, nestedReadPkg, parentOrderRow,
      leftMidHalfOrder⟩

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

theorem RationalIntervalPacket_regseqrat_handoff [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint consumer handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont endpoint consumer handoff ->
        UnaryHistory consumer ->
          PkgSig bundle handoff pkg ->
            UnaryHistory handoff ∧ hsame handoff (append endpoint consumer) ∧
              PkgSig bundle handoff pkg := by
  intro packet endpointConsumerHandoff consumerUnary handoffPkg
  rcases packet with
    ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
      _routeUnary, _provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder,
      _orderContainmentTransport, _transportRouteProvenance, _provenanceNameEndpoint,
      _endpointPkg⟩
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed endpointUnary consumerUnary endpointConsumerHandoff
  exact ⟨handoffUnary, endpointConsumerHandoff, handoffPkg⟩

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

theorem RationalIntervalPacket_standard_boundary_bridge [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint width containmentRead
      boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont left right width ->
        Cont containment route containmentRead ->
          Cont endpoint width boundary ->
            PkgSig bundle boundary pkg ->
              UnaryHistory width ∧ UnaryHistory containmentRead ∧ UnaryHistory boundary ∧
                hsame width order ∧ Cont endpoint width boundary ∧ PkgSig bundle boundary pkg := by
  intro packet widthRow containmentReadRow boundaryRow boundaryPkg
  obtain ⟨leftUnary, rightUnary, _orderUnary, containmentUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameUnary, endpointUnary, orderRow,
    _containmentRow, _provenanceRow, _endpointRow, _endpointPkg⟩ := packet
  have widthUnary : UnaryHistory width :=
    unary_cont_closed leftUnary rightUnary widthRow
  have sameWidthOrder : hsame width order :=
    cont_deterministic widthRow orderRow
  have containmentReadUnary : UnaryHistory containmentRead :=
    unary_cont_closed containmentUnary routeUnary containmentReadRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed endpointUnary widthUnary boundaryRow
  exact ⟨widthUnary, containmentReadUnary, boundaryUnary, sameWidthOrder, boundaryRow, boundaryPkg⟩

theorem RationalIntervalPacket_regseqrat_window_coverage [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint consumer handoff
      containmentRead boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont endpoint consumer handoff ->
        UnaryHistory consumer ->
          Cont containment route containmentRead ->
            Cont handoff containmentRead boundary ->
              PkgSig bundle boundary pkg ->
                UnaryHistory handoff ∧ UnaryHistory containmentRead ∧ UnaryHistory boundary ∧
                  hsame handoff (append endpoint consumer) ∧
                    Cont containment route containmentRead ∧
                      Cont handoff containmentRead boundary ∧ PkgSig bundle boundary pkg := by
  intro packet endpointConsumerHandoff consumerUnary containmentReadRow boundaryRow boundaryPkg
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, containmentUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder, _containmentRow,
    _provenanceRow, _endpointRow, _endpointPkg⟩ := packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed endpointUnary consumerUnary endpointConsumerHandoff
  have containmentReadUnary : UnaryHistory containmentRead :=
    unary_cont_closed containmentUnary routeUnary containmentReadRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed handoffUnary containmentReadUnary boundaryRow
  exact
    ⟨handoffUnary, containmentReadUnary, boundaryUnary, endpointConsumerHandoff,
      containmentReadRow, boundaryRow, boundaryPkg⟩

theorem RationalIntervalPacket_midpoint_bisection_window [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint midpoint leftOrder
      leftTransport leftProvenance leftEndpoint rightOrder rightTransport rightProvenance
      rightEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory midpoint ->
        Cont left midpoint leftOrder ->
          Cont leftOrder containment leftTransport ->
            Cont leftTransport route leftProvenance ->
              Cont leftProvenance name leftEndpoint ->
                PkgSig bundle leftEndpoint pkg ->
                  Cont midpoint right rightOrder ->
                    Cont rightOrder containment rightTransport ->
                      Cont rightTransport route rightProvenance ->
                        Cont rightProvenance name rightEndpoint ->
                          PkgSig bundle rightEndpoint pkg ->
                            RationalIntervalPacket left midpoint leftOrder containment
                                leftTransport route leftProvenance name leftEndpoint bundle pkg ∧
                              RationalIntervalPacket midpoint right rightOrder containment
                                  rightTransport route rightProvenance name rightEndpoint bundle
                                  pkg := by
  intro packet midpointUnary leftOrderRow leftTransportRow leftProvenanceRow leftEndpointRow
    leftPkg rightOrderRow rightTransportRow rightProvenanceRow rightEndpointRow rightPkg
  obtain ⟨leftUnary, rightUnary, _orderUnary, containmentUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameUnary, _endpointUnary, _leftRightOrder, _orderContainmentTransport,
    _transportRouteProvenance, _provenanceNameEndpoint, _endpointPkg⟩ := packet
  have leftOrderUnary : UnaryHistory leftOrder :=
    unary_cont_closed leftUnary midpointUnary leftOrderRow
  have leftTransportUnary : UnaryHistory leftTransport :=
    unary_cont_closed leftOrderUnary containmentUnary leftTransportRow
  have leftProvenanceUnary : UnaryHistory leftProvenance :=
    unary_cont_closed leftTransportUnary routeUnary leftProvenanceRow
  have leftEndpointUnary : UnaryHistory leftEndpoint :=
    unary_cont_closed leftProvenanceUnary nameUnary leftEndpointRow
  have rightOrderUnary : UnaryHistory rightOrder :=
    unary_cont_closed midpointUnary rightUnary rightOrderRow
  have rightTransportUnary : UnaryHistory rightTransport :=
    unary_cont_closed rightOrderUnary containmentUnary rightTransportRow
  have rightProvenanceUnary : UnaryHistory rightProvenance :=
    unary_cont_closed rightTransportUnary routeUnary rightProvenanceRow
  have rightEndpointUnary : UnaryHistory rightEndpoint :=
    unary_cont_closed rightProvenanceUnary nameUnary rightEndpointRow
  exact
    ⟨⟨leftUnary, midpointUnary, leftOrderUnary, containmentUnary, leftTransportUnary,
        routeUnary, leftProvenanceUnary, nameUnary, leftEndpointUnary, leftOrderRow,
        leftTransportRow, leftProvenanceRow, leftEndpointRow, leftPkg⟩,
      ⟨midpointUnary, rightUnary, rightOrderUnary, containmentUnary, rightTransportUnary,
        routeUnary, rightProvenanceUnary, nameUnary, rightEndpointUnary, rightOrderRow,
        rightTransportRow, rightProvenanceRow, rightEndpointRow, rightPkg⟩⟩

theorem RationalIntervalPacket_endpoint_transport_classifier [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint left' right'
      lowerClass upperClass order' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          Cont left left' lowerClass ->
            Cont right right' upperClass ->
              Cont left' right' order' ->
                UnaryHistory lowerClass ∧ UnaryHistory upperClass ∧ UnaryHistory order' ∧
                  hsame order order' ∧ Cont left' right' order' := by
  intro packet sameLeft sameRight lowerRow upperRow orderRow'
  obtain ⟨leftUnary, rightUnary, orderUnary, _containmentUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, _endpointUnary, orderRow,
    _containmentRow, _provenanceRow, _endpointRow, _endpointPkg⟩ := packet
  have leftUnary' : UnaryHistory left' :=
    unary_transport leftUnary sameLeft
  have rightUnary' : UnaryHistory right' :=
    unary_transport rightUnary sameRight
  have lowerUnary : UnaryHistory lowerClass :=
    unary_cont_closed leftUnary leftUnary' lowerRow
  have upperUnary : UnaryHistory upperClass :=
    unary_cont_closed rightUnary rightUnary' upperRow
  have sameOrder : hsame order order' :=
    cont_respects_hsame sameLeft sameRight orderRow orderRow'
  have orderUnary' : UnaryHistory order' :=
    unary_transport orderUnary sameOrder
  exact ⟨lowerUnary, upperUnary, orderUnary', sameOrder, orderRow'⟩

theorem RationalIntervalRefinement_choice_neutrality [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint choiceA choiceB :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont endpoint route choiceA ->
        Cont endpoint route choiceB ->
          PkgSig bundle choiceA pkg ->
            PkgSig bundle choiceB pkg ->
              UnaryHistory choiceA ∧ UnaryHistory choiceB ∧ hsame choiceA choiceB ∧
                PkgSig bundle choiceA pkg ∧ PkgSig bundle choiceB pkg := by
  intro packet choiceRowA choiceRowB choicePkgA choicePkgB
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameUnary, endpointUnary, _orderRow,
    _containmentRow, _provenanceRow, _endpointRow, _endpointPkg⟩ := packet
  have choiceUnaryA : UnaryHistory choiceA :=
    unary_cont_closed endpointUnary routeUnary choiceRowA
  have choiceUnaryB : UnaryHistory choiceB :=
    unary_cont_closed endpointUnary routeUnary choiceRowB
  have sameChoice : hsame choiceA choiceB :=
    cont_deterministic choiceRowA choiceRowB
  exact ⟨choiceUnaryA, choiceUnaryB, sameChoice, choicePkgA, choicePkgB⟩

end BEDC.Derived.RationalIntervalUp
