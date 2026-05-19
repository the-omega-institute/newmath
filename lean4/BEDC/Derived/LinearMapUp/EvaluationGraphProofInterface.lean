import BEDC.Derived.LinearMapUp.EvaluationGraphComposition

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LinearMapEvaluationGraphCompositionProofInterface {f g x y y' : BHist} :
    LinearMapSingletonCarrier f ->
      LinearMapSingletonCarrier g ->
        LinearMapSingletonCarrier x ->
          LinearMapSingletonClassifier y y' ->
            Cont (LinearMapSingletonEval f x) y y' ->
              SemanticNameCert LinearMapSingletonCarrier LinearMapSingletonCarrier
                    LinearMapSingletonCarrier LinearMapSingletonClassifier ∧
                LinearMapSingletonCarrier (LinearMapSingletonEval (LinearMapSingletonComp g f) x) ∧
                  LinearMapSingletonClassifier
                      (LinearMapSingletonEval (LinearMapSingletonComp g f) x) y' ∧
                    LinearMapSingletonClassifier (LinearMapSingletonComp g f) BHist.Empty := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrierF carrierG carrierX classifierYY' evalCont
  have closure :=
    LinearMapEvaluationGraph_composition_closure carrierF carrierG carrierX classifierYY' evalCont
  have laws := LinearMapSingleton_empty_history_laws
  exact ⟨laws.left, closure.left, closure.right.left, closure.right.right⟩

end BEDC.Derived.LinearMapUp
