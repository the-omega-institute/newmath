import BEDC.Derived.DiagonalRegularitySealUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalRegularitySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiagonalRegularitySealCarrier_nonescape
    {x : DiagonalRegularitySealUp} {endpointRead middleRead terminalRead : BHist} :
    (∃ representative endpointLeft endpointRight middleModulus dyadicTolerance finiteWindow
      regularityWitness terminalSeal transport routes provenance nameCert : BHist,
      x = DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
        dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
        nameCert ∧
        UnaryHistory representative ∧ UnaryHistory endpointLeft ∧ UnaryHistory middleModulus ∧
          UnaryHistory terminalSeal ∧
            Cont representative endpointLeft endpointRead ∧
              Cont endpointRead middleModulus middleRead ∧
                Cont middleRead terminalSeal terminalRead) →
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
                    UnaryHistory endpointRead ∧ UnaryHistory middleRead ∧
                      UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro accepted
  obtain ⟨representative, endpointLeft, endpointRight, middleModulus, dyadicTolerance,
    finiteWindow, regularityWitness, terminalSeal, transport, routes, provenance, nameCert,
    packetEq, representativeUnary, endpointLeftUnary, middleModulusUnary, terminalSealUnary,
    endpointRoute, middleRoute, terminalRoute⟩ := accepted
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed representativeUnary endpointLeftUnary endpointRoute
  have middleReadUnary : UnaryHistory middleRead :=
    unary_cont_closed endpointReadUnary middleModulusUnary middleRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed middleReadUnary terminalSealUnary terminalRoute
  subst packetEq
  have representativeMem :
      List.Mem (diagonalRegularitySealEncodeBHist representative)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) := by
    simp only [diagonalRegularitySealToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  have endpointLeftMem :
      List.Mem (diagonalRegularitySealEncodeBHist endpointLeft)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) := by
    simp only [diagonalRegularitySealToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  have endpointRightMem :
      List.Mem (diagonalRegularitySealEncodeBHist endpointRight)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) := by
    simp only [diagonalRegularitySealToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  have middleModulusMem :
      List.Mem (diagonalRegularitySealEncodeBHist middleModulus)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) := by
    simp only [diagonalRegularitySealToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  have dyadicToleranceMem :
      List.Mem (diagonalRegularitySealEncodeBHist dyadicTolerance)
        (diagonalRegularitySealToEventFlow
          (DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
            dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
            nameCert)) := by
    simp only [diagonalRegularitySealToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  exact
    ⟨representative, endpointLeft, endpointRight, middleModulus, dyadicTolerance, finiteWindow,
      regularityWitness, terminalSeal, transport, routes, provenance, nameCert, rfl,
      representativeMem, endpointLeftMem, endpointRightMem, middleModulusMem,
      dyadicToleranceMem, endpointReadUnary, middleReadUnary, terminalReadUnary⟩

end BEDC.Derived.DiagonalRegularitySealUp
