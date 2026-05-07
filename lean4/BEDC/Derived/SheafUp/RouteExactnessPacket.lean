import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist

def SheafRootRouteExactnessPacket
    (ambient member overlap route germ point openHist sectionHist endpoint restrictedOpen
      restrictedGermA restrictedGermB chartEndpoint : BHist) : Prop :=
  SheafBHistCoverNerveLedger ambient member overlap route germ ∧
    SheafBHistPointGermLedger point openHist sectionHist endpoint ∧
      SheafDownstreamConsumerScope point openHist sectionHist sectionHist endpoint endpoint
        restrictedOpen restrictedGermA restrictedGermB chartEndpoint

end BEDC.Derived.SheafUp
