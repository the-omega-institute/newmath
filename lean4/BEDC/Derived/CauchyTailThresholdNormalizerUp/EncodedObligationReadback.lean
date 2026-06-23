import BEDC.Derived.CauchyTailThresholdNormalizerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyTailThresholdNormalizerEncodedObligationReadback [AskSetup] [PackageSetup]
    (T : CauchyTailThresholdNormalizerUp)
    {S M Theta W0 W1 D R A E H C P L N terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchyTailThresholdNormalizerFields T =
        [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N] →
      Cont S M Theta →
        Cont Theta W0 W1 →
          Cont W1 D R →
            Cont R A E →
              Cont E C terminalRead →
                PkgSig bundle P pkg →
                  List.Mem Theta (cauchyTailThresholdNormalizerFields T) ∧
                    List.Mem W0 (cauchyTailThresholdNormalizerFields T) ∧
                      List.Mem W1 (cauchyTailThresholdNormalizerFields T) ∧
                        List.Mem D (cauchyTailThresholdNormalizerFields T) ∧
                          List.Mem R (cauchyTailThresholdNormalizerFields T) ∧
                            List.Mem A (cauchyTailThresholdNormalizerFields T) ∧
                              Cont S M Theta ∧ Cont Theta W0 W1 ∧ Cont W1 D R ∧
                                Cont R A E ∧ Cont E C terminalRead ∧
                                  PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  intro fields sourceRoute thresholdRoute readbackRoute agreementRoute terminalRoute pkgSig
  rw [fields]
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
      sourceRoute, thresholdRoute, readbackRoute, agreementRoute, terminalRoute, pkgSig⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
