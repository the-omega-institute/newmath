import BEDC.Derived.GroupUp.TerminalProduct

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem GroupUp_StdBridge :
    SemanticNameCert GroupSingletonCarrier GroupSingletonCarrier GroupSingletonCarrier
        GroupSingletonClassifier ∧
      GroupSingletonCarrier BHist.Empty ∧
      (∀ {x y : BHist}, GroupSingletonCarrier x → GroupSingletonCarrier y →
        GroupSingletonCarrier (GroupSingletonMul x y) ∧
          GroupSingletonClassifier (GroupSingletonMul x y) BHist.Empty) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x →
        GroupSingletonCarrier (GroupSingletonInv x) ∧
          GroupSingletonClassifier (GroupSingletonInv x) BHist.Empty) ∧
      (∀ {L R Q S : BHist}, GroupSingletonCarrier L → GroupSingletonCarrier R →
        (GroupSingletonClassifier (append L Q) (append R S) ↔
          GroupSingletonClassifier Q S)) := by
  have laws := GroupSingletonHistory_laws
  have terminal := GroupSingleton_terminal_standard_bridge
  constructor
  · exact terminal.left
  · constructor
    · exact terminal.right.left
    · constructor
      · intro x y carrierX carrierY
        have productCarrier : GroupSingletonCarrier (GroupSingletonMul x y) :=
          laws.right.left carrierX carrierY
        exact And.intro productCarrier
          (terminal.right.right.right.left carrierX carrierY)
      · constructor
        · intro x carrierX
          have inverseCarrier : GroupSingletonCarrier (GroupSingletonInv x) :=
            laws.right.right.left carrierX
          exact And.intro inverseCarrier
            (terminal.right.right.right.right carrierX)
        · intro L R Q S carrierL carrierR
          exact GroupSingletonClassifier_append_context_cancel_iff carrierL carrierR

end BEDC.Derived.GroupUp
