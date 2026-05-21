import BEDC.Derived.RealTailAgreementSealUp.TerminalRoute

namespace BEDC.Derived.RealTailAgreementSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealTailAgreementSealCarrier_shared_tail_budget_extraction
    {R S W D A H C P N leftRead rightRead leftDyadic rightDyadic agreement terminal
      budgetRead : BHist} :
    RealTailAgreementSealCarrier R S W D A H C P N →
      RealTailAgreementSealTerminalRoute R S W D A P leftRead rightRead leftDyadic
          rightDyadic agreement terminal →
        Cont terminal P budgetRead →
          UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory A ∧ UnaryHistory agreement ∧
            UnaryHistory terminal ∧ UnaryHistory budgetRead ∧ Cont W D leftDyadic ∧
              Cont W D rightDyadic ∧ Cont leftDyadic A agreement ∧
                Cont agreement P terminal ∧ Cont terminal P budgetRead ∧
                  hsame agreement (append leftDyadic A) ∧
                    hsame budgetRead (append terminal P) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier route terminalBudget
  obtain ⟨_unaryR, _unaryS, unaryW, unaryD, unaryA, _unaryH, _unaryC, _unaryP,
    _unaryN, _sourceWindow, _windowAgreement, _agreementRoutes, _provenanceSame⟩ :=
    carrier
  have summary :=
    RealTailAgreementSealTerminalRoute_exhaustion
      (R := R) (S := S) (W := W) (D := D) (A := A) (P := P)
      (leftRead := leftRead) (rightRead := rightRead) (leftDyadic := leftDyadic)
      (rightDyadic := rightDyadic) (agreement := agreement) (terminal := terminal) route
  have agreementUnary : UnaryHistory agreement :=
    summary.right.right.left
  have terminalUnary : UnaryHistory terminal :=
    summary.right.right.right.left
  have leftRoute : Cont W D leftDyadic :=
    summary.right.right.right.right.left
  have rightRoute : Cont W D rightDyadic :=
    summary.right.right.right.right.right.left
  have agreementRoute : Cont leftDyadic A agreement :=
    summary.right.right.right.right.right.right.left
  have terminalRoute : Cont agreement P terminal :=
    summary.right.right.right.right.right.right.right.left
  have agreementSame : hsame agreement (append leftDyadic A) :=
    summary.right.right.right.right.right.right.right.right
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed terminalUnary _unaryP terminalBudget
  exact
    ⟨unaryW, unaryD, unaryA, agreementUnary, terminalUnary, budgetUnary, leftRoute,
      rightRoute, agreementRoute, terminalRoute, terminalBudget, agreementSame,
      terminalBudget⟩

end BEDC.Derived.RealTailAgreementSealUp
