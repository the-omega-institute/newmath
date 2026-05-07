import BEDC.Derived.SheafUp.JointConsumerFace
import BEDC.Derived.SheafUp.RootProjection

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

theorem SheafDownstreamConsumption_joint_exhaustion
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint common chartOut : BHist} {sections : List BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafSchemeChartGluingTrace point common sections chartOut ->
        Cont restrictedOpen sectionA restrictedGermA ∧
          Cont restrictedOpen sectionB restrictedGermB ∧
            SheafRootJointConsumerFace restrictedOpen restrictedGermA ∧
              SheafRootJointConsumerFace restrictedOpen restrictedGermB ∧
                SheafRootJointConsumerFace point chartOut ∧ UnaryHistory chartOut := by
  intro scope chartTrace
  have projection :=
    SheafRootRingedSpaceConsumerProjection_scope (point := point) (openHist := openHist)
      (sectionA := sectionA) (sectionB := sectionB) (germA := germA) (germB := germB)
      (restrictedOpen := restrictedOpen) (restrictedGermA := restrictedGermA)
      (restrictedGermB := restrictedGermB) (chartEndpoint := chartEndpoint) scope
  have faceA : SheafRootJointConsumerFace restrictedOpen restrictedGermA :=
    SheafRootJointConsumerFace.faceRead projection.right.right.right.right.right.left
  have faceB : SheafRootJointConsumerFace restrictedOpen restrictedGermB :=
    SheafRootJointConsumerFace.faceRead projection.right.right.right.right.right.right.left
  have chartFace : SheafRootJointConsumerFace point chartOut :=
    SheafRootJointConsumerFace.chartTrace chartTrace
  have chartUnary : UnaryHistory chartOut :=
    SheafSchemeChartGluingTrace_unary_result chartTrace
  exact And.intro projection.right.right.left
    (And.intro projection.right.right.right.left
      (And.intro faceA
        (And.intro faceB
          (And.intro chartFace chartUnary))))

theorem SheafDownstreamConsumer_exactness_coverage
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint endpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafRootJointConsumerFace restrictedOpen endpoint ->
        SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
            restrictedOpen sectionB restrictedGermB restrictedOpen ∧
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
  have comparisonRows :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
          restrictedOpen sectionB restrictedGermB restrictedOpen ∧
        Cont restrictedOpen sectionA restrictedGermA ∧
          Cont restrictedOpen sectionB restrictedGermB :=
    SheafBHistPointGermLedger_common_open_comparison carrierRows.left
      carrierRows.right.left carrierRows.right.right.right.right.left
  have faceExhaustion :
      (∃ landing : SheafRootFaceLanding, SheafRootFaceRead restrictedOpen endpoint landing ∧
        (landing = SheafRootFaceLanding.coverMembership ∨
          landing = SheafRootFaceLanding.restrictionRoute ∨
            landing = SheafRootFaceLanding.localityGluingRefinement)) ∨
      (∃ common : BHist, ∃ sections : List BHist,
        SheafSchemeChartGluingTrace restrictedOpen common sections endpoint ∧
          UnaryHistory endpoint) :=
    SheafRootJointConsumerFace_exhaustion face
  exact And.intro comparisonRows.left
    (And.intro carrierRows.right.right.right.right.left
      (And.intro carrierRows.right.right.right.right.right faceExhaustion))

end BEDC.Derived.SheafUp
