import BEDC.Derived.SheafUp.DownstreamConsumption
import BEDC.Derived.SheafUp.RootCoverDescent

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafSchemeConsumption_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint common chartOut : BHist} {sections : List BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafSchemeChartGluingTrace point common sections chartOut ->
        SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
            restrictedOpen sectionB restrictedGermB restrictedOpen ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧
                SheafRootJointConsumerFace point chartOut ∧ UnaryHistory chartOut := by
  intro scope chartTrace
  have descent :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
          restrictedOpen sectionB restrictedGermB restrictedOpen ∧
        Cont restrictedOpen sectionA restrictedGermA ∧
          Cont restrictedOpen sectionB restrictedGermB ∧
            hsame restrictedGermA restrictedGermB ∧ hsame chartEndpoint restrictedGermB :=
    SheafRootCoverDescent_downstream_interface scope
  have consumption :
      Cont restrictedOpen sectionA restrictedGermA ∧
        Cont restrictedOpen sectionB restrictedGermB ∧
          SheafRootJointConsumerFace restrictedOpen restrictedGermA ∧
            SheafRootJointConsumerFace restrictedOpen restrictedGermB ∧
              SheafRootJointConsumerFace point chartOut ∧ UnaryHistory chartOut :=
    SheafDownstreamConsumption_joint_exhaustion scope chartTrace
  exact And.intro descent.left
    (And.intro descent.right.left
      (And.intro descent.right.right.left
        (And.intro descent.right.right.right.left
          consumption.right.right.right.right)))

end BEDC.Derived.SheafUp
