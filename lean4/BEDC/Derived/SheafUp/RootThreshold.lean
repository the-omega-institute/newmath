import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SheafRootThreshold_carrier_classifier_semantic_certificate
    {ambient member overlap route germ localRoute localGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      Cont member localRoute localGerm -> hsame route localRoute ->
        SemanticNameCert
            (fun endpoint : BHist =>
              SheafBHistPointGermLedger ambient member localRoute endpoint)
            (fun endpoint : BHist =>
              SheafBHistPointGermLedger ambient member localRoute endpoint)
            (fun endpoint : BHist =>
              SheafBHistPointGermLedger ambient member localRoute endpoint)
            hsame ∧
          SheafBHistPointGermLedger ambient member localRoute localGerm ∧
            hsame germ localGerm := by
  intro ledger localRow sameRoute
  have readback :
      SheafBHistPointGermLedger ambient member localRoute localGerm ∧
        hsame germ localGerm :=
    SheafBHistCoverNerveLedger_gluing_readback ledger localRow sameRoute
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger ambient member localRoute endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger ambient member localRoute endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger ambient member localRoute endpoint)
        hsame :=
    SheafRestrictedOpenCarrier_semantic_name_certificate readback.left
  exact And.intro cert readback

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

end BEDC.Derived.SheafUp
