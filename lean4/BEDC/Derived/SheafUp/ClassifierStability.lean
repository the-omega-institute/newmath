import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafDownstreamConsumer_classifier_stability
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint chartEndpoint' : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      hsame chartEndpoint chartEndpoint' ->
        SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
          SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
            Cont restrictedOpen sectionA restrictedGermA ∧
              Cont restrictedOpen sectionB restrictedGermB ∧
                hsame restrictedGermA restrictedGermB ∧
                  hsame chartEndpoint' restrictedGermB := by
  intro scope sameEndpoint
  have carrierScope :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧ hsame chartEndpoint restrictedGermB :=
    SheafDownstreamConsumer_carrier_scope scope
  exact And.intro carrierScope.left
    (And.intro carrierScope.right.left
      (And.intro carrierScope.right.right.left
        (And.intro carrierScope.right.right.right.left
          (And.intro carrierScope.right.right.right.right.left
            (hsame_trans (hsame_symm sameEndpoint)
              carrierScope.right.right.right.right.right)))))

end BEDC.Derived.SheafUp
