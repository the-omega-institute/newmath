import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

theorem SchemeAffineCoverLedger_exactness_obligation
    {point openHist sectionHist germ ringEndpoint chartEndpoint : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      CommRingSingletonClassifier ringEndpoint chartEndpoint ->
        SheafBHistPointGermLedger point openHist sectionHist germ ∧
          Cont openHist sectionHist germ ∧
            CommRingSingletonCarrier ringEndpoint ∧
              CommRingSingletonCarrier chartEndpoint ∧
                hsame ringEndpoint chartEndpoint ∧ TopologySingletonOpenAt openHist point := by
  intro surface chartClassifier
  exact And.intro surface.right.left
    (And.intro surface.right.left.right.right
      (And.intro chartClassifier.left
        (And.intro chartClassifier.right.left
          (And.intro chartClassifier.right.right surface.left))))

end BEDC.Derived.SchemeUp
