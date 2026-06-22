import BEDC.Derived.CauchyTailThresholdNormalizerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyTailThresholdCompositionScope
    (T : CauchyTailThresholdNormalizerUp)
    {S M Theta W0 W1 D R A E H C P L N terminalRead : BHist} :
    cauchyTailThresholdNormalizerFields T =
        [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N] ->
      UnaryHistory S ->
        UnaryHistory M ->
          UnaryHistory Theta ->
            UnaryHistory W0 ->
              UnaryHistory W1 ->
                UnaryHistory D ->
                  UnaryHistory R ->
                    UnaryHistory A ->
                      UnaryHistory E ->
                        UnaryHistory C ->
                          Cont S M Theta ->
                            Cont Theta W0 W1 ->
                              Cont W1 D R ->
                                Cont R A E ->
                                  Cont E C terminalRead ->
                                    List.Mem Theta (cauchyTailThresholdNormalizerFields T) ∧
                                      List.Mem W0 (cauchyTailThresholdNormalizerFields T) ∧
                                        List.Mem W1
                                            (cauchyTailThresholdNormalizerFields T) ∧
                                          List.Mem D
                                              (cauchyTailThresholdNormalizerFields T) ∧
                                            List.Mem R
                                                (cauchyTailThresholdNormalizerFields T) ∧
                                              List.Mem A
                                                  (cauchyTailThresholdNormalizerFields T) ∧
                                                UnaryHistory terminalRead ∧
                                                  Cont E C terminalRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fields _sourceUnary _sealUnary _thresholdUnary _leftWindowUnary rightWindowUnary
    toleranceUnary readbackUnary agreementUnary realUnary replayUnary _sourceRoute
    _thresholdRoute readbackRoute agreementRoute terminalRoute
  rw [fields]
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed realUnary replayUnary terminalRoute
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
      List.Mem.tail S
        (List.Mem.tail M
          (List.Mem.tail Theta
            (List.Mem.tail W0
              (List.Mem.tail W1
                (List.Mem.tail D (List.Mem.tail R (List.Mem.head _))))))),
      terminalUnary, terminalRoute⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
