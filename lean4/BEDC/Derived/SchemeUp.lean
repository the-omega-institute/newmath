import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp

theorem SchemeAffineCoverClassifier_overlap_locality
    {point openA openB sectionA sectionB germA germB ringA ringB chartA chartB common : BHist} :
    RingedSpaceSingletonSurface point openA sectionA germA ringA ->
      RingedSpaceSingletonSurface point openB sectionB germB ringB ->
        SheafBHistPointGermComparison point openA sectionA germA openB sectionB germB common ->
          CommRingSingletonClassifier chartA ringA ->
            CommRingSingletonClassifier chartB ringB ->
              hsame germA germB ∧ CommRingSingletonCarrier ringA ∧
                CommRingSingletonCarrier ringB := by
  intro _surfaceA _surfaceB comparison chartAClassified chartBClassified
  exact And.intro comparison.right.right.right.right.right.right.right.right
    (And.intro chartAClassified.right.left chartBClassified.right.left)

end BEDC.Derived.SchemeUp
