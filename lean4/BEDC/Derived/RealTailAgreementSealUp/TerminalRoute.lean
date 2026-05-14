import BEDC.Derived.RealTailAgreementSealUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealTailAgreementSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def RealTailAgreementSealTerminalRoute
    (R S W D A P leftRead rightRead leftDyadic rightDyadic agreement terminal : BHist) :
    Prop :=
  UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory A ∧ UnaryHistory P ∧
    Cont W D leftDyadic ∧ Cont W D rightDyadic ∧ Cont leftDyadic A agreement ∧
      Cont agreement P terminal ∧
        ∃ packet : RealTailAgreementSealUp,
          packet =
            RealTailAgreementSealUp.mk R S W D A leftRead rightRead agreement terminal

theorem RealTailAgreementSealTerminalRoute_exhaustion
    {R S W D A P leftRead rightRead leftDyadic rightDyadic agreement terminal : BHist} :
    RealTailAgreementSealTerminalRoute R S W D A P leftRead rightRead leftDyadic
      rightDyadic agreement terminal →
      UnaryHistory leftDyadic ∧ UnaryHistory rightDyadic ∧ UnaryHistory agreement ∧
        UnaryHistory terminal ∧ Cont W D leftDyadic ∧ Cont W D rightDyadic ∧
          Cont leftDyadic A agreement ∧ Cont agreement P terminal ∧
            hsame agreement (append leftDyadic A) := by
  -- BEDC touchpoint anchor: BHist Cont
  intro route
  cases route with
  | intro unaryW routeTail =>
      cases routeTail with
      | intro unaryD routeTail =>
          cases routeTail with
          | intro unaryA routeTail =>
              cases routeTail with
              | intro unaryP routeTail =>
                  cases routeTail with
                  | intro leftCont routeTail =>
                      cases routeTail with
                      | intro rightCont routeTail =>
                          cases routeTail with
                          | intro agreementCont routeTail =>
                              cases routeTail with
                              | intro terminalCont packetWitness =>
                                  cases packetWitness with
                                  | intro packet packetEq =>
                                      cases packetEq
                                      have unaryLeftDyadic : UnaryHistory leftDyadic :=
                                        unary_cont_closed unaryW unaryD leftCont
                                      have unaryRightDyadic : UnaryHistory rightDyadic :=
                                        unary_cont_closed unaryW unaryD rightCont
                                      have unaryAgreement : UnaryHistory agreement :=
                                        unary_cont_closed unaryLeftDyadic unaryA agreementCont
                                      have unaryTerminal : UnaryHistory terminal :=
                                        unary_cont_closed unaryAgreement unaryP terminalCont
                                      constructor
                                      · exact unaryLeftDyadic
                                      · constructor
                                        · exact unaryRightDyadic
                                        · constructor
                                          · exact unaryAgreement
                                          · constructor
                                            · exact unaryTerminal
                                            · constructor
                                              · exact leftCont
                                              · constructor
                                                · exact rightCont
                                                · constructor
                                                  · exact agreementCont
                                                  · constructor
                                                    · exact terminalCont
                                                    · exact agreementCont

theorem RealTailAgreementSeal_budget_route_uniqueness
    {R S W D A P leftRead rightRead leftDyadic rightDyadic agreement terminal : BHist} :
    RealTailAgreementSealTerminalRoute R S W D A P leftRead rightRead leftDyadic
      rightDyadic agreement terminal →
      hsame agreement (append leftDyadic A) ∧ hsame terminal (append agreement P) ∧
        Cont W D leftDyadic ∧ Cont W D rightDyadic ∧ Cont leftDyadic A agreement ∧
          Cont agreement P terminal := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro route
  cases route with
  | intro unaryW routeTail =>
      cases routeTail with
      | intro unaryD routeTail =>
          cases routeTail with
          | intro unaryA routeTail =>
              cases routeTail with
              | intro unaryP routeTail =>
                  cases routeTail with
                  | intro leftCont routeTail =>
                      cases routeTail with
                      | intro rightCont routeTail =>
                          cases routeTail with
                          | intro agreementCont routeTail =>
                              cases routeTail with
                              | intro terminalCont packetWitness =>
                                  cases packetWitness with
                                  | intro packet packetEq =>
                                      cases packetEq
                                      constructor
                                      · exact agreementCont
                                      · constructor
                                        · exact terminalCont
                                        · constructor
                                          · exact leftCont
                                          · constructor
                                            · exact rightCont
                                            · constructor
                                              · exact agreementCont
                                              · exact terminalCont

theorem RealTailAgreementSealTerminalRoute_root_source_window_admission
    {R S W D A P leftRead rightRead leftDyadic rightDyadic agreement terminal : BHist}
    (route : RealTailAgreementSealTerminalRoute R S W D A P leftRead rightRead leftDyadic
      rightDyadic agreement terminal) :
    UnaryHistory W ∧ UnaryHistory leftDyadic ∧ UnaryHistory rightDyadic ∧
      UnaryHistory agreement ∧ Cont W D leftDyadic ∧ Cont W D rightDyadic ∧
        Cont leftDyadic A agreement ∧ hsame agreement (append (append W D) A) := by
  -- BEDC touchpoint anchor: BHist Cont
  have summary :=
    RealTailAgreementSealTerminalRoute_exhaustion route
  have unaryW : UnaryHistory W :=
    route.left
  have unaryLeft : UnaryHistory leftDyadic :=
    summary.left
  have unaryRight : UnaryHistory rightDyadic :=
    summary.right.left
  have unaryAgreement : UnaryHistory agreement :=
    summary.right.right.left
  have leftCont : Cont W D leftDyadic :=
    summary.right.right.right.right.left
  have rightCont : Cont W D rightDyadic :=
    summary.right.right.right.right.right.left
  have agreementCont : Cont leftDyadic A agreement :=
    summary.right.right.right.right.right.right.left
  have sourceWindow : hsame leftDyadic (append W D) :=
    leftCont
  have agreementWindow : hsame agreement (append (append W D) A) := by
    cases sourceWindow
    exact agreementCont
  exact
    ⟨unaryW, unaryLeft, unaryRight, unaryAgreement, leftCont, rightCont, agreementCont,
      agreementWindow⟩

theorem RealTailAgreementSealCarrier_root_selector_consumer_totality
    {R S W D A P leftRead rightRead leftDyadic rightDyadic agreement terminal
      publicRead : BHist} :
    RealTailAgreementSealTerminalRoute R S W D A P leftRead rightRead leftDyadic
        rightDyadic agreement terminal →
      Cont terminal P publicRead →
        UnaryHistory agreement ∧ UnaryHistory terminal ∧ UnaryHistory publicRead ∧
          hsame agreement (append leftDyadic A) ∧ hsame publicRead (append terminal P) ∧
            Cont agreement P terminal ∧ Cont terminal P publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro route terminalPublic
  have summary :=
    RealTailAgreementSealTerminalRoute_exhaustion route
  have unaryAgreement : UnaryHistory agreement :=
    summary.right.right.left
  have unaryTerminal : UnaryHistory terminal :=
    summary.right.right.right.left
  have agreementSame : hsame agreement (append leftDyadic A) :=
    summary.right.right.right.right.right.right.right.right
  have agreementTerminal : Cont agreement P terminal :=
    summary.right.right.right.right.right.right.right.left
  have unaryP : UnaryHistory P :=
    route.right.right.right.left
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryTerminal unaryP terminalPublic
  exact
    ⟨unaryAgreement, unaryTerminal, unaryPublic, agreementSame, terminalPublic,
      agreementTerminal, terminalPublic⟩

end BEDC.Derived.RealTailAgreementSealUp
