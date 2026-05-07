import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafRootCoverDescent_downstream_interface
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
          restrictedOpen sectionB restrictedGermB restrictedOpen ∧
        Cont restrictedOpen sectionA restrictedGermA ∧
          Cont restrictedOpen sectionB restrictedGermB ∧
            hsame restrictedGermA restrictedGermB ∧ hsame chartEndpoint restrictedGermB := by
  intro scope
  have carrierScope :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧ hsame chartEndpoint restrictedGermB :=
    SheafDownstreamConsumer_carrier_scope scope
  have comparisonRows :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
          restrictedOpen sectionB restrictedGermB restrictedOpen ∧
        Cont restrictedOpen sectionA restrictedGermA ∧
          Cont restrictedOpen sectionB restrictedGermB :=
    SheafBHistPointGermLedger_common_open_comparison carrierScope.left carrierScope.right.left
      carrierScope.right.right.right.right.left
  exact And.intro comparisonRows.left
    (And.intro carrierScope.right.right.left
      (And.intro carrierScope.right.right.right.left
        (And.intro carrierScope.right.right.right.right.left
          carrierScope.right.right.right.right.right)))

end BEDC.Derived.SheafUp
