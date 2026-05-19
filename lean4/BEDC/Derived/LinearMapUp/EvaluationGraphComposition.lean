import BEDC.Derived.LinearMapUp.EvaluationGraphPackage

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem LinearMapEvaluationGraph_composition_closure {f g x y y' : BHist} :
    LinearMapSingletonCarrier f ->
      LinearMapSingletonCarrier g ->
        LinearMapSingletonCarrier x ->
          LinearMapSingletonClassifier y y' ->
            Cont (LinearMapSingletonEval f x) y y' ->
              LinearMapSingletonCarrier (LinearMapSingletonEval (LinearMapSingletonComp g f) x) ∧
                LinearMapSingletonClassifier (LinearMapSingletonEval (LinearMapSingletonComp g f) x)
                  y' ∧
                  LinearMapSingletonClassifier (LinearMapSingletonComp g f) BHist.Empty := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrierF carrierG carrierX classifierYY' evalCont
  have package :
      LinearMapSingletonCarrier y' ∧
        LinearMapSingletonClassifier (LinearMapSingletonEval f x) y' ∧
          LinearMapSingletonClassifier
            (LinearMapSingletonEval (LinearMapSingletonComp f f) x) y' :=
    LinearMapSingletonEvaluationGraph_package carrierF carrierX classifierYY' evalCont
  have exactness :
      LinearMapSingletonClassifier f BHist.Empty ∧
        LinearMapSingletonClassifier BHist.Empty BHist.Empty ∧
          LinearMapSingletonClassifier (LinearMapSingletonComp g f) BHist.Empty ∧
            LinearMapSingletonClassifier (LinearMapSingletonEval f x) x :=
    LinearMapSingleton_public_empty_code_exactness carrierF carrierG carrierX
  have laws := LinearMapSingleton_empty_history_laws
  have compCarrier : LinearMapSingletonCarrier (LinearMapSingletonComp g f) :=
    laws.right.right.right.left carrierG carrierF
  have compEvalRows :
      LinearMapSingletonCarrier (LinearMapSingletonEval (LinearMapSingletonComp g f) x) ∧
        LinearMapSingletonClassifier
          (LinearMapSingletonEval (LinearMapSingletonComp g f) x) BHist.Empty :=
    laws.right.right.left compCarrier carrierX
  have compEvalClassifier :
      LinearMapSingletonClassifier (LinearMapSingletonEval (LinearMapSingletonComp g f) x) y' :=
    And.intro compEvalRows.left
      (And.intro package.left (hsame_trans compEvalRows.left (hsame_symm package.left)))
  exact ⟨compEvalRows.left, compEvalClassifier, exactness.right.right.left⟩

end BEDC.Derived.LinearMapUp
