import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp

theorem SchemeSingleton_affine_cover_classifier_locality_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB ringEndpoint chartA chartB : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ->
      RingedSpaceSingletonSurface point openHist sectionB germB ringEndpoint ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              CommRingSingletonClassifier chartA chartB ->
                SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                    restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                  CommRingSingletonClassifier chartA chartB ∧
                    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ∧
                      RingedSpaceSingletonSurface point openHist sectionB germB ringEndpoint := by
  intro surfaceA surfaceB sameGerm sameOpen restrictedA restrictedB chartClassifier
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      surfaceA.right.left surfaceB.right.left sameGerm sameOpen restrictedA restrictedB
  exact And.intro comparison
    (And.intro chartClassifier
      (And.intro surfaceA surfaceB))

end BEDC.Derived.SchemeUp
