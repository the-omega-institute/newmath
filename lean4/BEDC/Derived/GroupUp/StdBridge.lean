import BEDC.Derived.GroupUp.TerminalProduct

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem GroupSingleton_terminal_standard_bridge :
    SemanticNameCert GroupSingletonCarrier GroupSingletonCarrier GroupSingletonCarrier
        GroupSingletonClassifier ∧
      GroupSingletonCarrier BHist.Empty ∧
      (∀ {h : BHist}, GroupSingletonCarrier h →
        GroupSingletonClassifier h BHist.Empty) ∧
      (∀ {x y : BHist}, GroupSingletonCarrier x → GroupSingletonCarrier y →
        GroupSingletonClassifier (GroupSingletonMul x y) BHist.Empty) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x →
        GroupSingletonClassifier (GroupSingletonInv x) BHist.Empty) := by
  have laws := GroupSingletonHistory_laws
  have terminal := GroupSingletonClassifier_terminal_package
  constructor
  · exact laws.left
  · constructor
    · exact hsame_refl BHist.Empty
    · constructor
      · intro h carrier
        exact (terminal.right.right h carrier).right.right
      · constructor
        · intro x y carrierX carrierY
          have productCarrier : GroupSingletonCarrier (GroupSingletonMul x y) :=
            laws.right.left carrierX carrierY
          exact (terminal.right.right (GroupSingletonMul x y) productCarrier).right.right
        · intro x carrierX
          have inverseCarrier : GroupSingletonCarrier (GroupSingletonInv x) :=
            laws.right.right.left carrierX
          exact (terminal.right.right (GroupSingletonInv x) inverseCarrier).right.right

end BEDC.Derived.GroupUp
