import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist

theorem LinearMapSingleton_pointwise_classifier_equivalence {f g : BHist} :
    (LinearMapSingletonClassifier f g <->
      LinearMapSingletonCarrier f ∧ LinearMapSingletonCarrier g ∧
        (forall {x : BHist}, LinearMapSingletonCarrier x ->
          LinearMapSingletonClassifier (LinearMapSingletonEval f x) (LinearMapSingletonEval g x))) ∧
      (LinearMapSingletonClassifier f g ->
        hsame (LinearMapSingletonEval f BHist.Empty) BHist.Empty ∧
          hsame (LinearMapSingletonEval g BHist.Empty) BHist.Empty) := by
  have emptyCarrier : LinearMapSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have evalClassified :
      LinearMapSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · constructor
    · intro classified
      exact And.intro classified.left
        (And.intro classified.right.left
          (by
            intro x _carrierX
            exact evalClassified))
    · intro pointwise
      have sameFG : hsame f g :=
        hsame_trans pointwise.left (hsame_symm pointwise.right.left)
      exact And.intro pointwise.left (And.intro pointwise.right.left sameFG)
  · intro _classified
    exact And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)

end BEDC.Derived.LinearMapUp
