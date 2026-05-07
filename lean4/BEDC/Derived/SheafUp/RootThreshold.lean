import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

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

end BEDC.Derived.SheafUp
