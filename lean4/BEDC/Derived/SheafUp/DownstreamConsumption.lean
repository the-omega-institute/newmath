import BEDC.Derived.SheafUp.JointConsumerFace
import BEDC.Derived.SheafUp.RootProjection

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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

end BEDC.Derived.SheafUp
