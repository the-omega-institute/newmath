import BEDC.Derived.DiagonalRegularitySealUp.TasteGate
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalRegularitySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalRegularitySealUp_window_factorization [AskSetup] [PackageSetup]
    {x : DiagonalRegularitySealUp} {endpointRead middleRead : BHist} :
    (∃ representative endpointLeft endpointRight middleModulus dyadicTolerance finiteWindow
      regularityWitness terminalSeal transport routes provenance nameCert : BHist,
      x = DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
        dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
        nameCert ∧
        UnaryHistory representative ∧ UnaryHistory endpointLeft ∧ UnaryHistory middleModulus ∧
          Cont representative endpointLeft endpointRead ∧
            Cont endpointRead middleModulus middleRead) →
      ∃ representative endpointLeft endpointRight middleModulus dyadicTolerance finiteWindow
        regularityWitness terminalSeal transport routes provenance nameCert : BHist,
        x = DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
          dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
          nameCert ∧
          List.Mem (diagonalRegularitySealEncodeBHist representative)
            (diagonalRegularitySealToEventFlow x) ∧
            List.Mem (diagonalRegularitySealEncodeBHist endpointLeft)
              (diagonalRegularitySealToEventFlow x) ∧
              List.Mem (diagonalRegularitySealEncodeBHist endpointRight)
                (diagonalRegularitySealToEventFlow x) ∧
                List.Mem (diagonalRegularitySealEncodeBHist middleModulus)
                  (diagonalRegularitySealToEventFlow x) ∧
                  List.Mem (diagonalRegularitySealEncodeBHist dyadicTolerance)
                    (diagonalRegularitySealToEventFlow x) ∧
                    UnaryHistory endpointRead ∧ UnaryHistory middleRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro accepted
  obtain ⟨representative, endpointLeft, endpointRight, middleModulus, dyadicTolerance,
    finiteWindow, regularityWitness, terminalSeal, transport, routes, provenance, nameCert,
    packetEq, representativeUnary, endpointLeftUnary, middleModulusUnary, endpointRoute,
    middleRoute⟩ := accepted
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed representativeUnary endpointLeftUnary endpointRoute
  have middleReadUnary : UnaryHistory middleRead :=
    unary_cont_closed endpointReadUnary middleModulusUnary middleRoute
  subst packetEq
  have representativeMem :
      List.Mem (diagonalRegularitySealEncodeBHist representative)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) :=
    List.Mem.tail [BEDC.FKernel.Mark.BMark.b0] (List.Mem.head _)
  have endpointLeftMem :
      List.Mem (diagonalRegularitySealEncodeBHist endpointLeft)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) :=
    List.Mem.tail [BEDC.FKernel.Mark.BMark.b0]
      (List.Mem.tail (diagonalRegularitySealEncodeBHist representative)
        (List.Mem.tail [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0]
          (List.Mem.head _)))
  have endpointRightMem :
      List.Mem (diagonalRegularitySealEncodeBHist endpointRight)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) :=
    List.Mem.tail [BEDC.FKernel.Mark.BMark.b0]
      (List.Mem.tail (diagonalRegularitySealEncodeBHist representative)
        (List.Mem.tail [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0]
          (List.Mem.tail (diagonalRegularitySealEncodeBHist endpointLeft)
            (List.Mem.tail
              [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
                BEDC.FKernel.Mark.BMark.b0]
              (List.Mem.head _)))))
  have middleModulusMem :
      List.Mem (diagonalRegularitySealEncodeBHist middleModulus)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) :=
    List.Mem.tail [BEDC.FKernel.Mark.BMark.b0]
      (List.Mem.tail (diagonalRegularitySealEncodeBHist representative)
        (List.Mem.tail [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0]
          (List.Mem.tail (diagonalRegularitySealEncodeBHist endpointLeft)
            (List.Mem.tail
              [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
                BEDC.FKernel.Mark.BMark.b0]
              (List.Mem.tail (diagonalRegularitySealEncodeBHist endpointRight)
                (List.Mem.tail
                  [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
                    BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0]
                  (List.Mem.head _)))))))
  have dyadicToleranceMem :
      List.Mem (diagonalRegularitySealEncodeBHist dyadicTolerance)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) :=
    List.Mem.tail [BEDC.FKernel.Mark.BMark.b0]
      (List.Mem.tail (diagonalRegularitySealEncodeBHist representative)
        (List.Mem.tail [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0]
          (List.Mem.tail (diagonalRegularitySealEncodeBHist endpointLeft)
            (List.Mem.tail
              [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
                BEDC.FKernel.Mark.BMark.b0]
              (List.Mem.tail (diagonalRegularitySealEncodeBHist endpointRight)
                (List.Mem.tail
                  [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
                    BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0]
                  (List.Mem.tail (diagonalRegularitySealEncodeBHist middleModulus)
                    (List.Mem.tail
                      [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
                        BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
                        BEDC.FKernel.Mark.BMark.b0]
                      (List.Mem.head _)))))))))
  exact
    ⟨representative, endpointLeft, endpointRight, middleModulus, dyadicTolerance, finiteWindow,
      regularityWitness, terminalSeal, transport, routes, provenance, nameCert, rfl,
      representativeMem, endpointLeftMem, endpointRightMem, middleModulusMem,
      dyadicToleranceMem, endpointReadUnary, middleReadUnary⟩

end BEDC.Derived.DiagonalRegularitySealUp
