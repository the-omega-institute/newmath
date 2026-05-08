import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

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

theorem LinearMapSingleton_terminal_standard_bridge {f g x : BHist} :
    LinearMapSingletonCarrier f ->
      LinearMapSingletonCarrier g ->
        LinearMapSingletonCarrier x ->
          SemanticNameCert LinearMapSingletonCarrier LinearMapSingletonCarrier
              LinearMapSingletonCarrier LinearMapSingletonClassifier ∧
            LinearMapSingletonClassifier f BHist.Empty ∧
            LinearMapSingletonClassifier BHist.Empty BHist.Empty ∧
            LinearMapSingletonClassifier (LinearMapSingletonComp g f) BHist.Empty ∧
            LinearMapSingletonClassifier (LinearMapSingletonEval f x) x ∧
            LinearMapSingletonCarrier (LinearMapSingletonEval f x) ∧
            hsame (LinearMapSingletonEval f x) BHist.Empty := by
  intro carrierF carrierG carrierX
  have laws := LinearMapSingleton_empty_history_laws
  have publicRows :
      LinearMapSingletonClassifier f BHist.Empty ∧
        LinearMapSingletonClassifier BHist.Empty BHist.Empty ∧
          LinearMapSingletonClassifier (LinearMapSingletonComp g f) BHist.Empty ∧
            LinearMapSingletonClassifier (LinearMapSingletonEval f x) x :=
    LinearMapSingleton_public_empty_code_exactness carrierF carrierG carrierX
  have evalRows :
      LinearMapSingletonCarrier (LinearMapSingletonEval f x) ∧
        LinearMapSingletonClassifier (LinearMapSingletonEval f x) BHist.Empty :=
    laws.right.right.left carrierF carrierX
  exact And.intro laws.left
    (And.intro publicRows.left
      (And.intro publicRows.right.left
        (And.intro publicRows.right.right.left
          (And.intro publicRows.right.right.right
            (And.intro evalRows.left evalRows.right.right.right)))))

end BEDC.Derived.LinearMapUp
