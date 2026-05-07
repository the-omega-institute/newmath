import BEDC.Derived.CommRingUp
import BEDC.Derived.RingedSpaceUp
import BEDC.Derived.TopologyUp.Singleton

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

def SchemeAffineChartSource
    (point openHist sectionHist germ ringEndpoint chartEndpoint : BHist) : Prop :=
  TopologySingletonOpenAt BHist.Empty point ∧
    RingedSpaceSingletonPackage point openHist sectionHist germ ringEndpoint ∧
      CommRingSingletonClassifier ringEndpoint chartEndpoint

theorem SchemeAffineChartSource_restriction_transport
    {point openHist sectionHist germ ringEndpoint chartEndpoint restrictedOpen
      restrictedGerm : BHist} :
    SchemeAffineChartSource point openHist sectionHist germ ringEndpoint chartEndpoint ->
      hsame openHist restrictedOpen -> Cont restrictedOpen sectionHist restrictedGerm ->
        SchemeAffineChartSource point restrictedOpen sectionHist restrictedGerm ringEndpoint
            chartEndpoint ∧
          hsame germ restrictedGerm := by
  intro source sameOpen restrictedRow
  have readback :
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm :=
    SheafBHistPointGermLedger_restriction_readback
      source.right.left.left sameOpen restrictedRow
  have package :
      RingedSpaceSingletonPackage point restrictedOpen sectionHist restrictedGerm ringEndpoint :=
    And.intro readback.left (And.intro source.right.left.right.left source.right.left.right.right)
  exact And.intro
    (And.intro source.left (And.intro package source.right.right))
    readback.right

end BEDC.Derived.SchemeUp
