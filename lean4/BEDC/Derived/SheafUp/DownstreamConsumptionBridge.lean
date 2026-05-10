import BEDC.Derived.SheafUp.DownstreamConsumptionBoundary
import BEDC.Derived.SheafUp.DownstreamConsumption

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SheafUp_StdBridge
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint schemeEndpoint pullbackEndpoint endpoint : BHist} :
    SheafDownstreamConsumptionBoundary point openHist sectionA sectionB germA germB
        restrictedOpen restrictedGermA restrictedGermB chartEndpoint schemeEndpoint
        pullbackEndpoint ->
      SheafRootJointConsumerFace restrictedOpen endpoint ->
        SemanticNameCert (SheafRootJointConsumerFace restrictedOpen)
            (SheafRootJointConsumerFace restrictedOpen)
            (SheafRootJointConsumerFace restrictedOpen) hsame ∧
          SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
            restrictedOpen sectionB restrictedGermB restrictedOpen ∧
          hsame schemeEndpoint restrictedGermA ∧ hsame pullbackEndpoint restrictedOpen := by
  intro boundary face
  have coverage :=
    SheafDownstreamConsumer_exactness_coverage
      (point := point) (openHist := openHist) (sectionA := sectionA)
      (sectionB := sectionB) (germA := germA) (germB := germB)
      (restrictedOpen := restrictedOpen) (restrictedGermA := restrictedGermA)
      (restrictedGermB := restrictedGermB) (chartEndpoint := chartEndpoint)
      boundary.left face
  exact And.intro (SheafRootJointConsumerFace_semantic_name_certificate face)
    (And.intro coverage.left (And.intro boundary.right.left boundary.right.right.left))

end BEDC.Derived.SheafUp
