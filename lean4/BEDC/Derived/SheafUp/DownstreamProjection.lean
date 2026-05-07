import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem SheafRootFaceRead_downstream_projection_separation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      Cont restrictedOpen sectionA restrictedGermA ∧
        Cont restrictedOpen sectionB restrictedGermB ∧
          SheafRootFaceRead restrictedOpen restrictedGermA .localityGluingRefinement ∧
            SheafRootFaceRead restrictedOpen restrictedGermB .localityGluingRefinement ∧
              hsame chartEndpoint restrictedGermB := by
  intro scope
  have rows :=
    SheafDownstreamConsumer_carrier_scope (point := point) (openHist := openHist)
      (sectionA := sectionA) (sectionB := sectionB) (germA := germA) (germB := germB)
      (restrictedOpen := restrictedOpen) (restrictedGermA := restrictedGermA)
      (restrictedGermB := restrictedGermB) (chartEndpoint := chartEndpoint) scope
  exact And.intro rows.right.right.left
    (And.intro rows.right.right.right.left
      (And.intro
        (SheafRootFaceRead.localityGluingRefinement rows.right.right.left
          rows.right.right.right.left rows.right.right.right.right.left)
        (And.intro
          (SheafRootFaceRead.localityGluingRefinement rows.right.right.right.left
            rows.right.right.left (hsame_symm rows.right.right.right.right.left))
          rows.right.right.right.right.right)))

end BEDC.Derived.SheafUp
