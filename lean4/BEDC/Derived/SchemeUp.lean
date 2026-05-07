import BEDC.Derived.CommRingUp
import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

def SchemeAffineChartLedger
    (point openHist sectionHist germ ringEndpoint chartEndpoint : BHist) : Prop :=
  RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ∧
    CommRingSingletonClassifier ringEndpoint chartEndpoint

theorem SchemeAffineChartLedger_carrier_source_obligation
    {point openHist sectionHist germ ringEndpoint chartEndpoint : BHist} :
    SchemeAffineChartLedger point openHist sectionHist germ ringEndpoint chartEndpoint ->
      TopologySingletonCarrier point ∧
        SheafBHistPointGermLedger point openHist sectionHist germ ∧
          Cont openHist sectionHist germ ∧
            CommRingSingletonCarrier ringEndpoint ∧
              CommRingSingletonCarrier chartEndpoint ∧
                hsame ringEndpoint chartEndpoint ∧ hsame chartEndpoint BHist.Empty := by
  intro ledger
  exact And.intro ledger.left.left.right
    (And.intro ledger.left.right.left
      (And.intro ledger.left.right.left.right.right
        (And.intro ledger.right.left
          (And.intro ledger.right.right.left
            (And.intro ledger.right.right.right ledger.right.right.left)))))

end BEDC.Derived.SchemeUp
