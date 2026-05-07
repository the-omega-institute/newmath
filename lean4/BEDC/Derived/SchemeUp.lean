import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp

theorem SchemeClassifier_locality_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartA chartB : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA chartA ->
      RingedSpaceSingletonSurface point openHist sectionB germB chartB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              CommRingSingletonClassifier chartA chartB ->
                SheafBHistPointGermComparison point restrictedOpen sectionA
                  restrictedGermA restrictedOpen sectionB restrictedGermB
                    restrictedOpen ∧ hsame restrictedGermA restrictedGermB ∧
                      CommRingSingletonClassifier chartA chartB := by
  intro surfaceA surfaceB sameGerm sameOpen restrictedA restrictedB chartRow
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      surfaceA.right.left surfaceB.right.left sameGerm sameOpen restrictedA restrictedB
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      surfaceA.right.left surfaceB.right.left sameGerm sameOpen restrictedA restrictedB
  exact And.intro comparison (And.intro descent.right.right chartRow)

end BEDC.Derived.SchemeUp
