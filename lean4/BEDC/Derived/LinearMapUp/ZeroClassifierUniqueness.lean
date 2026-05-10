import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist

theorem LinearMapSingleton_zero_classifier_uniqueness {f g : BHist} :
    LinearMapSingletonClassifier f BHist.Empty ->
      LinearMapSingletonClassifier g BHist.Empty ->
        LinearMapSingletonClassifier f g := by
  intro classifiedF classifiedG
  exact And.intro classifiedF.left
    (And.intro classifiedG.left
      (hsame_trans classifiedF.right.right (hsame_symm classifiedG.right.right)))

end BEDC.Derived.LinearMapUp
