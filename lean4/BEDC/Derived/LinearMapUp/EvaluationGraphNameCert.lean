import BEDC.Derived.LinearMapUp.EvaluationGraphPackage
import BEDC.Derived.LinearMapUp.PointwiseClassifier

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LinearMapEvaluationGraphNameCertObligations {f g x y y' : BHist} :
    LinearMapSingletonCarrier f ->
      LinearMapSingletonCarrier g ->
        LinearMapSingletonCarrier x ->
          LinearMapSingletonClassifier y y' ->
            SemanticNameCert LinearMapSingletonCarrier LinearMapSingletonCarrier
                LinearMapSingletonCarrier LinearMapSingletonClassifier ∧
              LinearMapSingletonClassifier (LinearMapSingletonEval f x) x ∧
                LinearMapSingletonCarrier (LinearMapSingletonEval f x) ∧
                  LinearMapSingletonClassifier (LinearMapSingletonComp g f) BHist.Empty := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame Cont
  intro carrierF carrierG carrierX classifierYY'
  have bridge :=
    LinearMapSingleton_terminal_standard_bridge carrierF carrierG carrierX
  have evalYCont : Cont (LinearMapSingletonEval f x) y y' := by
    change y' = append BHist.Empty y
    exact Eq.trans (hsame_symm classifierYY'.right.right) (append_empty_left y).symm
  have package :=
    LinearMapSingletonEvaluationGraph_package carrierF carrierX classifierYY' evalYCont
  have evalCarrierFromPackage : LinearMapSingletonCarrier (LinearMapSingletonEval f x) :=
    package.right.left.left
  exact
    ⟨bridge.left, bridge.right.right.right.right.left, evalCarrierFromPackage,
      bridge.right.right.right.left⟩

end BEDC.Derived.LinearMapUp
