import BEDC.Derived.RealTailAgreementSealUp.TerminalRoute

namespace BEDC.Derived.RealTailAgreementSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealTailAgreementSealCarrier_real_completion_handoff
    {R S W D A H C P N leftRead rightRead leftDyadic rightDyadic agreement terminal
      publicRead : BHist} :
    RealTailAgreementSealCarrier R S W D A H C P N →
      RealTailAgreementSealTerminalRoute R S W D A P leftRead rightRead leftDyadic
        rightDyadic agreement terminal →
        Cont terminal P publicRead →
          UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory A ∧ UnaryHistory agreement ∧
            UnaryHistory terminal ∧ UnaryHistory publicRead ∧ Cont W D leftDyadic ∧
              Cont W D rightDyadic ∧ Cont leftDyadic A agreement ∧ Cont agreement P terminal ∧
                Cont terminal P publicRead ∧ hsame agreement (append leftDyadic A) ∧
                  hsame publicRead (append terminal P) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro _carrier route terminalPublic
  have summary :=
    RealTailAgreementSealTerminalRoute_exhaustion route
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed summary.right.right.right.left route.right.right.right.left terminalPublic
  exact
    ⟨route.left, route.right.left, route.right.right.left, summary.right.right.left,
      summary.right.right.right.left, publicUnary, summary.right.right.right.right.left,
      summary.right.right.right.right.right.left,
      summary.right.right.right.right.right.right.left,
      summary.right.right.right.right.right.right.right.left, terminalPublic,
      summary.right.right.right.right.right.right.right.right, terminalPublic⟩

end BEDC.Derived.RealTailAgreementSealUp
