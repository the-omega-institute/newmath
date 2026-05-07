import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp

theorem SchemeAffineCoverLedger_overlap_classifier_locality
    {point openA openB sectionA sectionB germA germB ringA ringB chartA chartB common :
      BHist} :
    RingedSpaceSingletonSurface point openA sectionA germA ringA ->
      RingedSpaceSingletonSurface point openB sectionB germB ringB ->
        SheafBHistPointGermComparison point openA sectionA germA openB sectionB germB
          common ->
          CommRingSingletonClassifier ringA chartA ->
            CommRingSingletonClassifier ringB chartB ->
              CommRingSingletonClassifier chartA chartB ∧ Cont common sectionA germA ∧
                Cont common sectionB germB ∧ hsame germA germB := by
  intro surfaceA surfaceB comparison chartAClassified chartBClassified
  have ringAEmpty : hsame ringA BHist.Empty := surfaceA.right.right.right.right
  have ringBEmpty : hsame ringB BHist.Empty := surfaceB.right.right.right.right
  have sameCharts : hsame chartA chartB :=
    hsame_trans (hsame_symm chartAClassified.right.right)
      (hsame_trans ringAEmpty
        (hsame_trans (hsame_symm ringBEmpty) chartBClassified.right.right))
  exact And.intro
    (And.intro chartAClassified.right.left
      (And.intro chartBClassified.right.left sameCharts))
    (And.intro comparison.right.right.right.right.right.right.left
      (And.intro comparison.right.right.right.right.right.right.right.left
        comparison.right.right.right.right.right.right.right.right))

end BEDC.Derived.SchemeUp
