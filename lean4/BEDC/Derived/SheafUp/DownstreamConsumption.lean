import BEDC.Derived.SheafUp.JointConsumerFace

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafDownstreamConsumption_boundary_joint_exhaustion
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint endpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafRootJointConsumerFace restrictedOpen endpoint ->
        SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
          SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
            hsame restrictedGermA restrictedGermB ∧ hsame chartEndpoint restrictedGermB ∧
              ((∃ landing : SheafRootFaceLanding,
                  SheafRootFaceRead restrictedOpen endpoint landing ∧
                    (landing = SheafRootFaceLanding.coverMembership ∨
                      landing = SheafRootFaceLanding.restrictionRoute ∨
                        landing = SheafRootFaceLanding.localityGluingRefinement)) ∨
                (∃ common : BHist, ∃ sections : List BHist,
                  SheafSchemeChartGluingTrace restrictedOpen common sections endpoint ∧
                    UnaryHistory endpoint)) := by
  intro scope face
  have carrierRows :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧
                hsame chartEndpoint restrictedGermB :=
    SheafDownstreamConsumer_carrier_scope (point := point) (openHist := openHist)
      (sectionA := sectionA) (sectionB := sectionB) (germA := germA) (germB := germB)
      (restrictedOpen := restrictedOpen) (restrictedGermA := restrictedGermA)
      (restrictedGermB := restrictedGermB) (chartEndpoint := chartEndpoint) scope
  have faceExhaustion :
      (∃ landing : SheafRootFaceLanding, SheafRootFaceRead restrictedOpen endpoint landing ∧
        (landing = SheafRootFaceLanding.coverMembership ∨
          landing = SheafRootFaceLanding.restrictionRoute ∨
            landing = SheafRootFaceLanding.localityGluingRefinement)) ∨
      (∃ common : BHist, ∃ sections : List BHist,
        SheafSchemeChartGluingTrace restrictedOpen common sections endpoint ∧
          UnaryHistory endpoint) :=
    SheafRootJointConsumerFace_exhaustion face
  exact And.intro carrierRows.left
    (And.intro carrierRows.right.left
      (And.intro carrierRows.right.right.right.right.left
        (And.intro carrierRows.right.right.right.right.right faceExhaustion)))

end BEDC.Derived.SheafUp
