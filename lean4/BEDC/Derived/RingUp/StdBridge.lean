import BEDC.Derived.RingUp

namespace BEDC.Derived.RingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RingUp_StdBridge :
    SemanticNameCert RingSingletonCarrier RingSingletonCarrier RingSingletonCarrier
        RingSingletonClassifier ∧
      (forall {x y : BHist}, RingSingletonCarrier x -> RingSingletonCarrier y ->
        RingSingletonClassifier (RingSingletonAdd x y) RingSingletonZero) ∧
      (forall {x y : BHist}, RingSingletonCarrier x -> RingSingletonCarrier y ->
        RingSingletonClassifier (RingSingletonMul x y) RingSingletonOne) ∧
      (forall {x y z : BHist}, RingSingletonCarrier x -> RingSingletonCarrier y ->
        RingSingletonCarrier z ->
          RingSingletonClassifier (RingSingletonMul x (RingSingletonAdd y z))
            (RingSingletonAdd (RingSingletonMul x y) (RingSingletonMul x z))) := by
  have laws := RingSingletonEmptyHistory_laws
  constructor
  · exact laws.left
  · constructor
    · exact laws.right.left
    · constructor
      · intro x y carrierX carrierY
        exact laws.right.right.right.left carrierX carrierY
      · exact laws.right.right.right.right.left

end BEDC.Derived.RingUp
