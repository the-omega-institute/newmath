import BEDC.Derived.CauchyTailThresholdNormalizerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyTailThresholdNormalizerTailWindowInduction
    (T : CauchyTailThresholdNormalizerUp)
    {S M Theta W0 W1 D R A E H C P L N terminalRead : BHist} :
    cauchyTailThresholdNormalizerFields T =
        [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N] →
      UnaryHistory Theta →
        UnaryHistory W0 →
          UnaryHistory D →
            UnaryHistory A →
              UnaryHistory C →
                Cont Theta W0 W1 →
                  Cont W1 D R →
                    Cont R A E →
                      Cont E C terminalRead →
                        List.Mem Theta (cauchyTailThresholdNormalizerFields T) ∧
                          List.Mem W0 (cauchyTailThresholdNormalizerFields T) ∧
                            List.Mem W1 (cauchyTailThresholdNormalizerFields T) ∧
                              List.Mem D (cauchyTailThresholdNormalizerFields T) ∧
                                List.Mem R (cauchyTailThresholdNormalizerFields T) ∧
                                  UnaryHistory W1 ∧ UnaryHistory R ∧ UnaryHistory E ∧
                                    UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fields thetaUnary w0Unary toleranceUnary agreementUnary replayUnary thresholdRoute
    readbackRoute agreementRoute terminalRoute
  rw [fields]
  have w1Unary : UnaryHistory W1 :=
    unary_cont_closed thetaUnary w0Unary thresholdRoute
  have rUnary : UnaryHistory R :=
    unary_cont_closed w1Unary toleranceUnary readbackRoute
  have eUnary : UnaryHistory E :=
    unary_cont_closed rUnary agreementUnary agreementRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed eUnary replayUnary terminalRoute
  exact
    ⟨List.Mem.tail S (List.Mem.tail M (List.Mem.head _)),
      List.Mem.tail S (List.Mem.tail M (List.Mem.tail Theta (List.Mem.head _))),
      List.Mem.tail S
        (List.Mem.tail M
          (List.Mem.tail Theta (List.Mem.tail W0 (List.Mem.head _)))),
      List.Mem.tail S
        (List.Mem.tail M
          (List.Mem.tail Theta
            (List.Mem.tail W0 (List.Mem.tail W1 (List.Mem.head _))))),
      List.Mem.tail S
        (List.Mem.tail M
          (List.Mem.tail Theta
            (List.Mem.tail W0
              (List.Mem.tail W1 (List.Mem.tail D (List.Mem.head _)))))),
      w1Unary, rUnary, eUnary, terminalUnary⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
