import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CantorSetCarrier_endpoint_ledger_stability [AskSetup] [PackageSetup]
    {T G I D R E T' G' I' D' prefixRead prefixRead' endpointRead
      endpointRead' : BHist}
    (sameT : hsame T T') (sameG : hsame G G') (sameI : hsame I I')
    (sameD : hsame D D') (leftPrefix : Cont T G prefixRead)
    (rightPrefix : Cont T' G' prefixRead')
    (leftEndpoint : Cont prefixRead D endpointRead)
    (rightEndpoint : Cont prefixRead' D' endpointRead') :
    hsame prefixRead prefixRead' ∧ hsame endpointRead endpointRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  have samePrefix : hsame prefixRead prefixRead' :=
    cont_respects_hsame sameT sameG leftPrefix rightPrefix
  have sameEndpoint : hsame endpointRead endpointRead' :=
    cont_respects_hsame samePrefix sameD leftEndpoint rightEndpoint
  exact And.intro samePrefix sameEndpoint

end BEDC.Derived.CantorSetUp
