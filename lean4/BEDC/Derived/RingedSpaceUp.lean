import BEDC.Derived.CommRingUp
import BEDC.Derived.SheafUp
import BEDC.Derived.TopologyUp.Singleton

namespace BEDC.Derived.RingedSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

theorem RingedSpaceSingleton_cover_nerve_empty_boundary
    {point ambient member overlap route germ operationA operationB : BHist} :
    TopologySingletonOpenAt BHist.Empty point ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ->
        hsame germ BHist.Empty ->
          CommRingSingletonClassifier operationA operationB ->
            hsame overlap BHist.Empty ∧ hsame route BHist.Empty ∧
              CommRingSingletonClassifier operationA operationB ∧
                TopologySingletonOpenAt BHist.Empty point := by
  intro openPoint ledger germEmpty commOps
  have boundary := SheafBHistCoverNerveLedger_empty_boundary ledger germEmpty
  exact And.intro boundary.left
    (And.intro boundary.right
      (And.intro commOps openPoint))

theorem RingedSpaceSingleton_sheaf_commring_stalk_locality_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB operationA operationB : BHist} :
    TopologySingletonOpenAt BHist.Empty point ->
      SheafBHistPointGermLedger point openHist sectionA germA ->
        SheafBHistPointGermLedger point openHist sectionB germB ->
          hsame germA germB -> hsame openHist restrictedOpen ->
            Cont restrictedOpen sectionA restrictedGermA ->
              Cont restrictedOpen sectionB restrictedGermB ->
                CommRingSingletonClassifier operationA operationB ->
                  SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                    SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                      hsame restrictedGermA restrictedGermB ∧
                        CommRingSingletonClassifier operationA operationB ∧
                          TopologySingletonOpenAt BHist.Empty point := by
  intro openPoint ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB commOps
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  exact And.intro descent.left
    (And.intro descent.right.left
      (And.intro descent.right.right
        (And.intro commOps openPoint)))

end BEDC.Derived.RingedSpaceUp
