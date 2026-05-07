import BEDC.Derived.CommRingUp
import BEDC.Derived.SheafUp
import BEDC.Derived.TopologyUp.Singleton

namespace BEDC.Derived.RingedSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CommRingUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

def RingedSpaceSingletonSurface
    (point openHist sectionHist germ ringEndpoint : BHist) : Prop :=
  TopologySingletonOpenAt openHist point ∧
    SheafBHistPointGermLedger point openHist sectionHist germ ∧
      CommRingSingletonClassifier ringEndpoint BHist.Empty

theorem RingedSpaceSingletonSurface_carrier_classifier_rows
    {point openHist sectionHist germ ringEndpoint : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      TopologySingletonCarrier point ∧ UnaryHistory point ∧ UnaryHistory openHist ∧
        Cont openHist sectionHist germ ∧ CommRingSingletonCarrier ringEndpoint ∧
          CommRingSingletonClassifier ringEndpoint BHist.Empty := by
  intro surface
  exact And.intro surface.left.right
    (And.intro surface.right.left.left
      (And.intro surface.right.left.right.left
        (And.intro surface.right.left.right.right
          (And.intro surface.right.right.left surface.right.right))))

end BEDC.Derived.RingedSpaceUp
