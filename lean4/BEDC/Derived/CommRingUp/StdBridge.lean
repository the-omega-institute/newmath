import BEDC.Derived.CommRingUp.SingletonAppend

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem CommRingUp_StdBridge :
    SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
        CommRingSingletonCarrier CommRingSingletonClassifier ∧
      CommRingSingletonCarrier CommRingSingletonZero ∧
      CommRingSingletonCarrier CommRingSingletonOne ∧
      (∀ {x y : BHist}, CommRingSingletonCarrier x -> CommRingSingletonCarrier y ->
        CommRingSingletonCarrier (CommRingSingletonAdd x y) ∧
          CommRingSingletonClassifier (CommRingSingletonAdd x y) BHist.Empty) ∧
      (∀ {x y : BHist}, CommRingSingletonCarrier x -> CommRingSingletonCarrier y ->
        CommRingSingletonCarrier (CommRingSingletonMul x y) ∧
          CommRingSingletonClassifier (CommRingSingletonMul x y) BHist.Empty) ∧
      (∀ {x y z : BHist}, CommRingSingletonCarrier x -> CommRingSingletonCarrier y ->
        CommRingSingletonCarrier z ->
          CommRingSingletonClassifier (CommRingSingletonMul x (CommRingSingletonAdd y z))
            (CommRingSingletonAdd (CommRingSingletonMul x y) (CommRingSingletonMul x z))) ∧
      (∀ {L R Q S : BHist}, CommRingSingletonCarrier L -> CommRingSingletonCarrier R ->
        (CommRingSingletonClassifier (append L Q) (append R S) <->
          CommRingSingletonClassifier Q S)) := by
  have laws := singleton_empty_history_commring_laws
  constructor
  · exact laws.left
  · constructor
    · exact hsame_refl BHist.Empty
    · constructor
      · exact hsame_refl BHist.Empty
      · constructor
        · intro x y carrierX carrierY
          exact And.intro (hsame_refl BHist.Empty) (laws.right.left carrierX carrierY)
        · constructor
          · intro x y carrierX carrierY
            exact And.intro (hsame_refl BHist.Empty)
              (laws.right.right.right.left carrierX carrierY)
          · constructor
            · intro x y z carrierX carrierY carrierZ
              exact laws.right.right.right.right.right.left carrierX carrierY carrierZ
            · intro L R Q S carrierL carrierR
              exact CommRingSingletonClassifier_append_context_cancel_iff carrierL carrierR

end BEDC.Derived.CommRingUp
