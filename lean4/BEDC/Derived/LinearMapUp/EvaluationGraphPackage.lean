import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem LinearMapSingletonEvaluationGraph_package {f x y y' : BHist} :
    LinearMapSingletonCarrier f ->
      LinearMapSingletonCarrier x ->
        LinearMapSingletonClassifier y y' ->
          Cont (LinearMapSingletonEval f x) y y' ->
            LinearMapSingletonCarrier y' ∧
              LinearMapSingletonClassifier (LinearMapSingletonEval f x) y' ∧
                LinearMapSingletonClassifier (LinearMapSingletonEval (LinearMapSingletonComp f f) x)
                  y' := by
  intro carrierF carrierX classifier continuation
  have laws := LinearMapSingleton_empty_history_laws
  have exactness :=
    LinearMapSingleton_public_empty_code_exactness carrierF carrierF carrierX
  have yCarrier : LinearMapSingletonCarrier y := classifier.left
  have yPrimeCarrier : LinearMapSingletonCarrier y' :=
    cont_respects_hsame (hsame_refl BHist.Empty) yCarrier continuation
      (cont_right_unit BHist.Empty)
  have evalRows :=
    laws.right.right.left carrierF carrierX
  have compEvalRows :=
    laws.right.right.left exactness.right.right.left.left carrierX
  have evalToYPrime : LinearMapSingletonClassifier (LinearMapSingletonEval f x) y' :=
    And.intro evalRows.left
      (And.intro yPrimeCarrier (hsame_trans evalRows.left (hsame_symm yPrimeCarrier)))
  have compEvalToYPrime :
      LinearMapSingletonClassifier (LinearMapSingletonEval (LinearMapSingletonComp f f) x) y' :=
    And.intro compEvalRows.left
      (And.intro yPrimeCarrier (hsame_trans compEvalRows.left (hsame_symm yPrimeCarrier)))
  exact And.intro yPrimeCarrier (And.intro evalToYPrime compEvalToYPrime)

end BEDC.Derived.LinearMapUp
