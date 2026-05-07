import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def SheafDownstreamConsumptionBoundary
    (point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint schemeEndpoint pullbackEndpoint : BHist) : Prop :=
  SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
      restrictedGermA restrictedGermB chartEndpoint ∧
    hsame schemeEndpoint restrictedGermA ∧ hsame pullbackEndpoint restrictedOpen ∧
      Cont restrictedOpen sectionA restrictedGermA

end BEDC.Derived.SheafUp
