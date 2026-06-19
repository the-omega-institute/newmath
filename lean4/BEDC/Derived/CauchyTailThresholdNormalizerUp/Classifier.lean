import BEDC.Derived.CauchyTailThresholdNormalizerUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def CauchyTailThresholdNormalizerClassifier
    (T U : CauchyTailThresholdNormalizerUp) : Prop :=
  ∃ S M Theta W0 W1 D R A E H C P L N
    S' M' Theta' W0' W1' D' R' A' E' H' C' P' L' N' : BHist,
    cauchyTailThresholdNormalizerFields T =
        [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N] ∧
      cauchyTailThresholdNormalizerFields U =
        [S', M', Theta', W0', W1', D', R', A', E', H', C', P', L', N'] ∧
        hsame Theta Theta' ∧ hsame W0 W0' ∧ hsame W1 W1' ∧
          Cont S M Theta ∧ Cont S' M' Theta'

theorem CauchyTailThresholdNormalizerClassifier_threshold_window_routes
    {T U : CauchyTailThresholdNormalizerUp} :
    CauchyTailThresholdNormalizerClassifier T U →
      ∃ S M Theta W0 W1 S' M' Theta' W0' W1' : BHist,
        List.Mem Theta (cauchyTailThresholdNormalizerFields T) ∧
          List.Mem W0 (cauchyTailThresholdNormalizerFields T) ∧
            List.Mem W1 (cauchyTailThresholdNormalizerFields T) ∧
              List.Mem Theta' (cauchyTailThresholdNormalizerFields U) ∧
                List.Mem W0' (cauchyTailThresholdNormalizerFields U) ∧
                  List.Mem W1' (cauchyTailThresholdNormalizerFields U) ∧
                    hsame Theta Theta' ∧ hsame W0 W0' ∧ hsame W1 W1' ∧
                      Cont S M Theta ∧ Cont S' M' Theta' := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro classified
  rcases classified with
    ⟨S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N,
      S', M', Theta', W0', W1', D', R', A', E', H', C', P', L', N',
      fieldsT, fieldsU, thresholdSame, leftWindowSame, rightWindowSame,
      sourceRoute, targetRoute⟩
  rw [fieldsT, fieldsU]
  exact
    ⟨S, M, Theta, W0, W1, S', M', Theta', W0', W1',
      List.Mem.tail S (List.Mem.tail M (List.Mem.head _)),
      List.Mem.tail S (List.Mem.tail M (List.Mem.tail Theta (List.Mem.head _))),
      List.Mem.tail S
        (List.Mem.tail M
          (List.Mem.tail Theta (List.Mem.tail W0 (List.Mem.head _)))),
      List.Mem.tail S' (List.Mem.tail M' (List.Mem.head _)),
      List.Mem.tail S' (List.Mem.tail M' (List.Mem.tail Theta' (List.Mem.head _))),
      List.Mem.tail S'
        (List.Mem.tail M'
          (List.Mem.tail Theta' (List.Mem.tail W0' (List.Mem.head _)))),
      thresholdSame, leftWindowSame, rightWindowSame, sourceRoute, targetRoute⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
