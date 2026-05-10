import BEDC.Derived.SheafUp.RootRouteExactness

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def SheafRootRouteExactnessPacket
    (ambient member overlap route germ point openHist sectionHist endpoint restrictedOpen
      restrictedGermA restrictedGermB chartEndpoint : BHist) : Prop :=
  SheafBHistCoverNerveLedger ambient member overlap route germ ∧
    SheafBHistPointGermLedger point openHist sectionHist endpoint ∧
      SheafDownstreamConsumerScope point openHist sectionHist sectionHist endpoint endpoint
        restrictedOpen restrictedGermA restrictedGermB chartEndpoint

theorem SheafRootRouteExactness_namecert_consumption
    {ambient member overlap route germ point openHist sectionHist endpoint restrictedOpen
      restrictedGermA restrictedGermB chartEndpoint routeWitness routeTarget finalGerm : BHist} :
    SheafRootRouteExactnessPacket ambient member overlap route germ point openHist sectionHist
      endpoint restrictedOpen restrictedGermA restrictedGermB chartEndpoint ->
        hsame openHist restrictedOpen ->
          Cont restrictedOpen routeWitness routeTarget ->
            hsame routeTarget restrictedOpen ->
              Cont routeTarget sectionHist finalGerm ->
                SheafRootRouteExactnessPacket ambient member overlap route germ point routeTarget
                    sectionHist finalGerm restrictedOpen restrictedGermA restrictedGermB
                    chartEndpoint ∧
                  hsame routeWitness BHist.Empty ∧ hsame endpoint finalGerm := by
  intro packet sameOpen routeRow sameTarget finalRow
  have scope := packet.right.right
  have stability :
      SheafBHistPointGermLedger point routeTarget sectionHist finalGerm ∧
        hsame finalGerm restrictedGermA ∧ hsame endpoint restrictedGermA :=
    SheafBHistPointGermLedger_route_history_target_classifier_stability
      packet.right.left sameOpen routeRow sameTarget finalRow
      scope.right.right.right.right.left
  have routeEmpty : hsame routeWitness BHist.Empty :=
    cont_right_unit_unique (cont_result_hsame_transport routeRow sameTarget)
  have sameEndpointFinal : hsame endpoint finalGerm :=
    hsame_trans stability.right.right (hsame_symm stability.right.left)
  have scopeAtTarget :
      SheafDownstreamConsumerScope point routeTarget sectionHist sectionHist finalGerm finalGerm
        restrictedOpen restrictedGermA restrictedGermB chartEndpoint :=
    And.intro stability.left
      (And.intro stability.left
        (And.intro (hsame_refl finalGerm)
          (And.intro sameTarget
            (And.intro scope.right.right.right.right.left
              (And.intro scope.right.right.right.right.right.left
                scope.right.right.right.right.right.right)))))
  exact And.intro
    (And.intro packet.left (And.intro stability.left scopeAtTarget))
    (And.intro routeEmpty sameEndpointFinal)

end BEDC.Derived.SheafUp
