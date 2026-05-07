import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp

theorem SchemeAffineCoverRow_semantic_name_certificate
    {point openHist sectionHist germ ringEndpoint chartEndpoint : BHist}
    (package : RingedSpaceSingletonPackage point openHist sectionHist germ ringEndpoint)
    (chart : CommRingSingletonClassifier chartEndpoint BHist.Empty) :
    SemanticNameCert
      (fun endpoint : BHist =>
        RingedSpaceSingletonPackage point openHist sectionHist germ endpoint ∧
          CommRingSingletonClassifier chartEndpoint BHist.Empty)
      (fun endpoint : BHist =>
        RingedSpaceSingletonPackage point openHist sectionHist germ endpoint ∧
          CommRingSingletonClassifier chartEndpoint BHist.Empty)
      (fun endpoint : BHist =>
        RingedSpaceSingletonPackage point openHist sectionHist germ endpoint ∧
          CommRingSingletonClassifier chartEndpoint BHist.Empty)
      hsame := by
  constructor
  · constructor
    · exact Exists.intro ringEndpoint (And.intro package chart)
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro endpoint endpoint' same
      exact hsame_symm same
    · intro endpoint endpoint' endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      cases same
      exact carrier
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

end BEDC.Derived.SchemeUp
