import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem GroupSingletonHistory_opposite_laws :
    let OppMul : BHist -> BHist -> BHist := fun x y => GroupSingletonMul y x
    SemanticNameCert GroupSingletonCarrier GroupSingletonCarrier GroupSingletonCarrier
        GroupSingletonClassifier ∧
      (∀ {x y : BHist}, GroupSingletonCarrier x -> GroupSingletonCarrier y ->
        GroupSingletonCarrier (OppMul x y)) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x ->
        GroupSingletonCarrier (GroupSingletonInv x)) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x ->
        GroupSingletonClassifier (OppMul GroupSingletonUnit x) x) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x ->
        GroupSingletonClassifier (OppMul x GroupSingletonUnit) x) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x ->
        GroupSingletonClassifier (OppMul (GroupSingletonInv x) x) GroupSingletonUnit) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x ->
        GroupSingletonClassifier (OppMul x (GroupSingletonInv x)) GroupSingletonUnit) := by
  dsimp
  have laws := GroupSingletonHistory_laws
  constructor
  · exact laws.left
  · constructor
    · intro x y carrierX carrierY
      exact laws.right.left carrierY carrierX
    · constructor
      · exact laws.right.right.left
      · constructor
        · intro x carrierX
          exact laws.right.right.right.right.left carrierX
        · constructor
          · intro x carrierX
            exact laws.right.right.right.left carrierX
          · constructor
            · intro x carrierX
              exact laws.right.right.right.right.right.right carrierX
            · intro x carrierX
              exact laws.right.right.right.right.right.left carrierX

end BEDC.Derived.GroupUp
