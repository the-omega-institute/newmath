import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

protected theorem CommRingUp_concrete_to_schema :
    SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
      CommRingSingletonCarrier CommRingSingletonClassifier ∧
      (∀ {x y : BHist}, CommRingSingletonCarrier x -> CommRingSingletonCarrier y ->
        CommRingSingletonClassifier (CommRingSingletonAdd x y) BHist.Empty) ∧
      (∀ {x y : BHist}, CommRingSingletonCarrier x -> CommRingSingletonCarrier y ->
        CommRingSingletonClassifier (CommRingSingletonMul x y) (CommRingSingletonMul y x)) := by
  have laws := singleton_empty_history_commring_laws
  exact And.intro laws.left (And.intro laws.right.left laws.right.right.right.left)

end BEDC.Derived.CommRingUp
