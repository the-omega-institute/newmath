import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

theorem GroupSingletonClassifier_inverse_empty_fiber_iff {x y : BHist} :
    GroupSingletonClassifier (GroupSingletonInv x) y <-> hsame y BHist.Empty := by
  dsimp [GroupSingletonClassifier, GroupSingletonCarrier, GroupSingletonInv]
  constructor
  · intro classified
    exact classified.right.left
  · intro endpoint
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro endpoint (hsame_symm endpoint))

end BEDC.Derived.GroupUp
