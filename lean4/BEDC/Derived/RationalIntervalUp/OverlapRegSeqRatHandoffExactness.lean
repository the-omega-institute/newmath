import BEDC.Derived.RationalIntervalUp
import BEDC.Derived.RationalIntervalUp.Refinement

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_overlap_regseqrat_handoff_exactness [AskSetup] [PackageSetup]
    {left1 right1 order1 containment1 transport1 route1 provenance1 name1 endpoint1 left2 right2
      order2 containment2 transport2 route2 provenance2 name2 endpoint2 left right order
      containment transport route provenance name endpoint consumer handoff containmentRead
      boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left1 right1 order1 containment1 transport1 route1 provenance1 name1
        endpoint1 bundle pkg →
      RationalIntervalPacket left2 right2 order2 containment2 transport2 route2 provenance2 name2
          endpoint2 bundle pkg →
        hsame left1 left →
          hsame right1 right →
            hsame containment1 containment →
              hsame route1 route →
                hsame name1 name →
                  hsame left2 left →
                    hsame right2 right →
                      hsame containment2 containment →
                        hsame route2 route →
                          hsame name2 name →
                            Cont left right order →
                              Cont order containment transport →
                                Cont transport route provenance →
                                  Cont provenance name endpoint →
                                    PkgSig bundle endpoint pkg →
                                      UnaryHistory consumer →
                                        Cont endpoint consumer handoff →
                                          Cont containment route containmentRead →
                                            Cont handoff containmentRead boundary →
                                              PkgSig bundle boundary pkg →
                                                RationalIntervalPacket left right order
                                                    containment transport route provenance name
                                                    endpoint bundle pkg ∧
                                                  UnaryHistory handoff ∧
                                                    UnaryHistory containmentRead ∧
                                                      UnaryHistory boundary ∧
                                                        hsame endpoint1 endpoint ∧
                                                          hsame endpoint2 endpoint ∧
                                                            PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig UnaryHistory
  intro packet1 packet2 sameLeft1 sameRight1 sameContainment1 sameRoute1 sameName1
    sameLeft2 sameRight2 sameContainment2 sameRoute2 sameName2 leftRightOrder
    orderContainmentTransport transportRouteProvenance provenanceNameEndpoint endpointPkg
    consumerUnary endpointConsumerHandoff containmentRouteRead handoffContainmentBoundary
    boundaryPkg
  have common :=
    RationalIntervalPacket_common_refinement_window packet1 packet2 sameLeft1 sameRight1
      sameContainment1 sameRoute1 sameName1 sameLeft2 sameRight2 sameContainment2 sameRoute2
      sameName2 leftRightOrder orderContainmentTransport transportRouteProvenance
      provenanceNameEndpoint endpointPkg
  rcases common with
    ⟨commonPacket, _sameOrder1, _sameOrder2, _sameTransport1, _sameTransport2,
      _sameProvenance1, _sameProvenance2, sameEndpoint1, sameEndpoint2⟩
  have coverage :=
    RationalIntervalPacket_regseqrat_window_coverage commonPacket endpointConsumerHandoff
      consumerUnary containmentRouteRead handoffContainmentBoundary boundaryPkg
  rcases coverage with
    ⟨handoffUnary, containmentReadUnary, boundaryUnary, _sameHandoff, _containmentRouteRead,
      _handoffContainmentBoundary, boundaryPkgOut⟩
  exact
    ⟨commonPacket, handoffUnary, containmentReadUnary, boundaryUnary, sameEndpoint1,
      sameEndpoint2, boundaryPkgOut⟩

end BEDC.Derived.RationalIntervalUp
