import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LinearMapUp_StdBridge :
    SemanticNameCert LinearMapSingletonCarrier LinearMapSingletonCarrier
        LinearMapSingletonCarrier LinearMapSingletonClassifier /\
      LinearMapSingletonCarrier BHist.Empty /\
      (forall {f x : BHist}, LinearMapSingletonCarrier f -> LinearMapSingletonCarrier x ->
        LinearMapSingletonCarrier (LinearMapSingletonEval f x) /\
          LinearMapSingletonClassifier (LinearMapSingletonEval f x) BHist.Empty) /\
      (forall {g f : BHist}, LinearMapSingletonCarrier g -> LinearMapSingletonCarrier f ->
        LinearMapSingletonCarrier (LinearMapSingletonComp g f)) /\
      (forall {f g x y : BHist}, LinearMapSingletonClassifier f g ->
        LinearMapSingletonClassifier x y ->
          LinearMapSingletonClassifier (LinearMapSingletonEval f x)
            (LinearMapSingletonEval g y)) /\
      (forall {f g x : BHist}, LinearMapSingletonCarrier f -> LinearMapSingletonCarrier g ->
        LinearMapSingletonCarrier x ->
          LinearMapSingletonClassifier (LinearMapSingletonComp g f) BHist.Empty /\
            LinearMapSingletonClassifier (LinearMapSingletonEval f x) x) := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame
  have laws := LinearMapSingleton_empty_history_laws
  constructor
  · exact laws.left
  · constructor
    · exact laws.right.left
    · constructor
      · exact laws.right.right.left
      · constructor
        · exact laws.right.right.right.left
        · constructor
          · exact laws.right.right.right.right
          · intro f g x carrierF carrierG carrierX
            have exactness :=
              LinearMapSingleton_public_empty_code_exactness carrierF carrierG carrierX
            exact ⟨exactness.right.right.left, exactness.right.right.right⟩

end BEDC.Derived.LinearMapUp
