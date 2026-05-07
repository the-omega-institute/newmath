import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp

theorem SchemeAffineChartLedger_overlap_locality_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartA chartB ringEndpointA ringEndpointB : BHist} :
    RingedSpaceSingletonPackage point openHist sectionA germA ringEndpointA ->
      RingedSpaceSingletonPackage point openHist sectionB germB ringEndpointB ->
        CommRingSingletonClassifier chartA ringEndpointA ->
          CommRingSingletonClassifier chartB ringEndpointB ->
            hsame germA germB ->
              hsame openHist restrictedOpen ->
                Cont restrictedOpen sectionA restrictedGermA ->
                  Cont restrictedOpen sectionB restrictedGermB ->
                    SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                      SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                        hsame restrictedGermA restrictedGermB ∧
                          CommRingSingletonClassifier chartA chartB := by
  intro packageA packageB chartClassA chartClassB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      packageA.left packageB.left sameGerm sameOpen restrictedA restrictedB
  have sameChart : hsame chartA chartB :=
    hsame_trans chartClassA.left (hsame_symm chartClassB.left)
  have chartClassifier : CommRingSingletonClassifier chartA chartB :=
    And.intro chartClassA.left
      (And.intro chartClassB.left sameChart)
  exact And.intro descent.left
    (And.intro descent.right.left (And.intro descent.right.right chartClassifier))

end BEDC.Derived.SchemeUp
