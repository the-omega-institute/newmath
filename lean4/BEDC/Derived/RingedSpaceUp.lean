import BEDC.Derived.CommRingUp
import BEDC.Derived.SheafUp

namespace BEDC.Derived.RingedSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CommRingUp
open BEDC.Derived.SheafUp

def RingedSpaceSingletonPackage
    (point openHist sectionHist germ ringEndpoint : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧
    CommRingSingletonCarrier sectionHist ∧
      CommRingSingletonClassifier sectionHist ringEndpoint

theorem RingedSpaceSingleton_carrier_sheaf_obligation
    {point openHist sectionHist germ ringEndpoint : BHist} :
    RingedSpaceSingletonPackage point openHist sectionHist germ ringEndpoint ->
      UnaryHistory point ∧ UnaryHistory openHist ∧ Cont openHist sectionHist germ ∧
        CommRingSingletonCarrier sectionHist ∧ CommRingSingletonCarrier ringEndpoint ∧
          hsame sectionHist ringEndpoint := by
  intro package
  exact And.intro package.left.left
    (And.intro package.left.right.left
      (And.intro package.left.right.right
        (And.intro package.right.left
          (And.intro package.right.right.right.left package.right.right.right.right))))

end BEDC.Derived.RingedSpaceUp
