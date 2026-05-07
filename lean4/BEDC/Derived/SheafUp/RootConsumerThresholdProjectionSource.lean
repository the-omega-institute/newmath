import BEDC.Derived.SheafUp.DownstreamProjection

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def SheafRootConsumerThresholdProjectionSource
    (_point _openHist sectionA sectionB _germA _germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist) : Prop :=
  SheafRootFaceRead restrictedOpen restrictedGermA SheafRootFaceLanding.restrictionRoute ∧
    SheafRootFaceRead restrictedOpen restrictedGermB SheafRootFaceLanding.restrictionRoute ∧
      Cont restrictedOpen sectionA restrictedGermA ∧
        Cont restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB ∧ hsame chartEndpoint restrictedGermB

theorem SheafRootConsumerThresholdProjectionSource_projection_faces
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafRootConsumerThresholdProjectionSource point openHist sectionA sectionB germA germB
        restrictedOpen restrictedGermA restrictedGermB chartEndpoint := by
  intro scope
  have projectionRows :=
    SheafRootConsumerRingedSpaceProjection_semantic_name_certificate
      (point := point) (openHist := openHist) (sectionA := sectionA) (sectionB := sectionB)
      (germA := germA) (germB := germB) (restrictedOpen := restrictedOpen)
      (restrictedGermA := restrictedGermA) (restrictedGermB := restrictedGermB)
      (chartEndpoint := chartEndpoint) scope
  have boundaryRows :=
    SheafDownstreamConsumer_RingedSpace_boundary_rows
      (point := point) (openHist := openHist) (sectionA := sectionA) (sectionB := sectionB)
      (germA := germA) (germB := germB) (restrictedOpen := restrictedOpen)
      (restrictedGermA := restrictedGermA) (restrictedGermB := restrictedGermB)
      (chartEndpoint := chartEndpoint) scope
  exact And.intro projectionRows.right.left
    (And.intro projectionRows.right.right.left
      (And.intro boundaryRows.right.right.right.left
        (And.intro boundaryRows.right.right.right.right
          (And.intro projectionRows.right.right.right boundaryRows.right.left))))

end BEDC.Derived.SheafUp
