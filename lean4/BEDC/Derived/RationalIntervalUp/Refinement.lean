import BEDC.Derived.RationalIntervalUp

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_refinement_choice_neutrality [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint choice choice' package
      package' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory choice ->
        UnaryHistory choice' ->
          hsame choice choice' ->
            Cont endpoint choice package ->
              Cont endpoint choice' package' ->
                PkgSig bundle package pkg ->
                  PkgSig bundle package' pkg ->
                    hsame package package' ∧ UnaryHistory package ∧ UnaryHistory package' ∧
                      Cont endpoint choice package ∧ Cont endpoint choice' package' ∧
                        PkgSig bundle package pkg ∧ PkgSig bundle package' pkg := by
  intro packet choiceUnary choiceUnary' sameChoice endpointChoicePackage endpointChoicePackage'
    packagePkg packagePkg'
  rcases packet with
    ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
      _routeUnary, _provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder,
      _orderContainmentTransport, _transportRouteProvenance, _provenanceNameEndpoint,
      _endpointPkg⟩
  have samePackage : hsame package package' :=
    cont_respects_hsame (hsame_refl endpoint) sameChoice endpointChoicePackage
      endpointChoicePackage'
  have packageUnary : UnaryHistory package :=
    unary_cont_closed endpointUnary choiceUnary endpointChoicePackage
  have packageUnary' : UnaryHistory package' :=
    unary_cont_closed endpointUnary choiceUnary' endpointChoicePackage'
  exact
    ⟨samePackage, packageUnary, packageUnary', endpointChoicePackage, endpointChoicePackage',
      packagePkg, packagePkg'⟩

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

theorem RationalIntervalPacket_refinement_normal_form [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint consumer readback bridge :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory consumer ->
        Cont endpoint consumer readback ->
          Cont endpoint readback bridge ->
            PkgSig bundle readback pkg ->
              PkgSig bundle bridge pkg ->
                UnaryHistory readback ∧ UnaryHistory bridge ∧ Cont endpoint consumer readback ∧
                  Cont endpoint readback bridge ∧ PkgSig bundle readback pkg ∧
                    PkgSig bundle bridge pkg := by
  intro packet consumerUnary endpointConsumerReadback endpointReadbackBridge readbackPkg bridgePkg
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder,
    _orderContainmentTransport, _transportRouteProvenance, _provenanceNameEndpoint,
    _endpointPkg⟩ := packet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed endpointUnary consumerUnary endpointConsumerReadback
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed endpointUnary readbackUnary endpointReadbackBridge
  exact
    ⟨readbackUnary, bridgeUnary, endpointConsumerReadback, endpointReadbackBridge, readbackPkg,
      bridgePkg⟩

theorem RationalIntervalPacket_nested_consumer_window_factorization [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint consumer readback
      nested basis boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory consumer ->
        Cont endpoint consumer readback ->
          Cont readback transport nested ->
            Cont consumer transport basis ->
              Cont endpoint basis boundary ->
                PkgSig bundle boundary pkg ->
                  UnaryHistory readback ∧ UnaryHistory nested ∧ UnaryHistory basis ∧
                    UnaryHistory boundary ∧ hsame nested boundary ∧
                      Cont endpoint consumer readback ∧ Cont readback transport nested ∧
                        Cont consumer transport basis ∧ Cont endpoint basis boundary ∧
                          PkgSig bundle boundary pkg := by
  intro packet consumerUnary endpointConsumerReadback readbackTransportNested
    consumerTransportBasis endpointBasisBoundary boundaryPkg
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder,
    _orderContainmentTransport, _transportRouteProvenance, _provenanceNameEndpoint,
    _endpointPkg⟩ := packet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed endpointUnary consumerUnary endpointConsumerReadback
  have nestedUnary : UnaryHistory nested :=
    unary_cont_closed readbackUnary transportUnary readbackTransportNested
  have basisUnary : UnaryHistory basis :=
    unary_cont_closed consumerUnary transportUnary consumerTransportBasis
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed endpointUnary basisUnary endpointBasisBoundary
  have sameNestedBoundary : hsame nested boundary :=
    cont_assoc_hsame endpointConsumerReadback readbackTransportNested consumerTransportBasis
      endpointBasisBoundary
  exact
    ⟨readbackUnary, nestedUnary, basisUnary, boundaryUnary, sameNestedBoundary,
      endpointConsumerReadback, readbackTransportNested, consumerTransportBasis,
      endpointBasisBoundary, boundaryPkg⟩

theorem RationalIntervalPacket_common_refinement_associativity [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint consumer basis
      leftAssoc midPair rightAssoc : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory consumer ->
        Cont endpoint containment basis ->
          Cont basis consumer leftAssoc ->
            Cont containment consumer midPair ->
              Cont endpoint midPair rightAssoc ->
                PkgSig bundle rightAssoc pkg ->
                  UnaryHistory basis ∧ UnaryHistory midPair ∧ UnaryHistory leftAssoc ∧
                    UnaryHistory rightAssoc ∧ hsame leftAssoc rightAssoc ∧
                      Cont endpoint containment basis ∧ Cont basis consumer leftAssoc ∧
                        Cont containment consumer midPair ∧ Cont endpoint midPair rightAssoc ∧
                          PkgSig bundle rightAssoc pkg := by
  intro packet consumerUnary endpointContainmentBasis basisConsumerLeftAssoc
    containmentConsumerMidPair endpointMidPairRightAssoc rightAssocPkg
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, containmentUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder,
    _orderContainmentTransport, _transportRouteProvenance, _provenanceNameEndpoint,
    _endpointPkg⟩ := packet
  have basisUnary : UnaryHistory basis :=
    unary_cont_closed endpointUnary containmentUnary endpointContainmentBasis
  have midPairUnary : UnaryHistory midPair :=
    unary_cont_closed containmentUnary consumerUnary containmentConsumerMidPair
  have leftAssocUnary : UnaryHistory leftAssoc :=
    unary_cont_closed basisUnary consumerUnary basisConsumerLeftAssoc
  have rightAssocUnary : UnaryHistory rightAssoc :=
    unary_cont_closed endpointUnary midPairUnary endpointMidPairRightAssoc
  have sameAssoc : hsame leftAssoc rightAssoc :=
    cont_assoc_hsame endpointContainmentBasis basisConsumerLeftAssoc containmentConsumerMidPair
      endpointMidPairRightAssoc
  exact
    ⟨basisUnary, midPairUnary, leftAssocUnary, rightAssocUnary, sameAssoc,
      endpointContainmentBasis, basisConsumerLeftAssoc, containmentConsumerMidPair,
      endpointMidPairRightAssoc, rightAssocPkg⟩

end BEDC.Derived.RationalIntervalUp
