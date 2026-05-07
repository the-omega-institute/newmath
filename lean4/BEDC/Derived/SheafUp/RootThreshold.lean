import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SheafRootThreshold_semantic_name_certificate
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
            restrictedOpen restrictedGermA restrictedGermB endpoint)
        (fun endpoint : BHist =>
          SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
            restrictedOpen restrictedGermA restrictedGermB endpoint)
        (fun endpoint : BHist =>
          SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
            restrictedOpen restrictedGermA restrictedGermB endpoint)
        hsame := by
  intro scope
  constructor
  · constructor
    · exact Exists.intro chartEndpoint scope
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro endpoint endpoint' same
      exact hsame_symm same
    · intro endpoint endpoint' endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      exact And.intro carrier.left
        (And.intro carrier.right.left
          (And.intro carrier.right.right.left
            (And.intro carrier.right.right.right.left
              (And.intro carrier.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.left
                  (hsame_trans (hsame_symm same)
                    carrier.right.right.right.right.right.right))))))
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

theorem SheafRootThreshold_downstream_coverage_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
            restrictedOpen sectionB restrictedGermB restrictedOpen ∧
            SheafRootFaceRead restrictedOpen restrictedGermA .restrictionRoute ∧
              SheafRootFaceRead restrictedOpen restrictedGermB .restrictionRoute ∧
                SemanticNameCert
                  (fun endpoint : BHist =>
                    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
                      restrictedOpen restrictedGermA restrictedGermB endpoint)
                  (fun endpoint : BHist =>
                    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
                      restrictedOpen restrictedGermA restrictedGermB endpoint)
                  (fun endpoint : BHist =>
                    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
                      restrictedOpen restrictedGermA restrictedGermB endpoint)
                  hsame := by
  intro scope
  have carrierScope :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧
                hsame chartEndpoint restrictedGermB :=
    SheafDownstreamConsumer_carrier_scope scope
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      carrierScope.left carrierScope.right.left carrierScope.right.right.right.right.left).left
  have readA : SheafRootFaceRead restrictedOpen restrictedGermA .restrictionRoute :=
    SheafRootFaceRead.restrictionRoute carrierScope.right.right.left
  have readB : SheafRootFaceRead restrictedOpen restrictedGermB .restrictionRoute :=
    SheafRootFaceRead.restrictionRoute carrierScope.right.right.right.left
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
            restrictedOpen restrictedGermA restrictedGermB endpoint)
        (fun endpoint : BHist =>
          SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
            restrictedOpen restrictedGermA restrictedGermB endpoint)
        (fun endpoint : BHist =>
          SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
            restrictedOpen restrictedGermA restrictedGermB endpoint)
        hsame :=
    SheafRootThreshold_semantic_name_certificate scope
  exact And.intro carrierScope.left
    (And.intro carrierScope.right.left
      (And.intro comparison
        (And.intro readA
          (And.intro readB cert))))

end BEDC.Derived.SheafUp
