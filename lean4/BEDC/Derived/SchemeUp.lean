import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

def SchemeSingletonPackage
    (point openHist sectionHist germ ringEndpoint chartEndpoint : BHist) : Prop :=
  RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ∧
    CommRingSingletonCarrier chartEndpoint ∧
      CommRingSingletonClassifier chartEndpoint ringEndpoint

theorem SchemeSingleton_carrier_source_obligation
    {point openHist sectionHist germ ringEndpoint chartEndpoint : BHist} :
    SchemeSingletonPackage point openHist sectionHist germ ringEndpoint chartEndpoint ->
      TopologySingletonOpenAt openHist point ∧
        SheafBHistPointGermLedger point openHist sectionHist germ ∧
          CommRingSingletonCarrier chartEndpoint ∧ CommRingSingletonCarrier ringEndpoint ∧
            hsame chartEndpoint BHist.Empty := by
  intro package
  exact And.intro package.left.left
    (And.intro package.left.right.left
      (And.intro package.right.left
        (And.intro package.right.right.right.left package.right.left)))

end BEDC.Derived.SchemeUp
