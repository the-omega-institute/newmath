import BEDC.Derived.DigestProvenancePacketUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.DigestProvenancePacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DigestProvenancePacketCarrier_source_fiber_ledger_order
    (R : DigestProvenancePacketUp) :
    ∃ V S F G E H C P N : BHist,
      R = DigestProvenancePacketUp.mk V S F G E H C P N ∧
        ∀ sourceFiber ledgerRead equalityGate : BHist,
          Cont S F sourceFiber →
            Cont sourceFiber G ledgerRead →
              Cont ledgerRead E equalityGate →
                UnaryHistory S →
                  UnaryHistory F →
                    UnaryHistory G →
                      UnaryHistory E →
                        UnaryHistory sourceFiber ∧ UnaryHistory ledgerRead ∧
                          UnaryHistory equalityGate ∧ Cont S F sourceFiber ∧
                            Cont sourceFiber G ledgerRead ∧
                              Cont ledgerRead E equalityGate ∧ hsame V V := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  cases R with
  | mk V S F G E H C P N =>
      refine ⟨V, S, F, G, E, H, C, P, N, rfl, ?_⟩
      intro sourceFiber ledgerRead equalityGate sourceFiberCont ledgerReadCont
        equalityGateCont sourceUnary fiberUnary gapUnary exactnessUnary
      have sourceFiberUnary : UnaryHistory sourceFiber :=
        unary_cont_closed sourceUnary fiberUnary sourceFiberCont
      have ledgerReadUnary : UnaryHistory ledgerRead :=
        unary_cont_closed sourceFiberUnary gapUnary ledgerReadCont
      have equalityGateUnary : UnaryHistory equalityGate :=
        unary_cont_closed ledgerReadUnary exactnessUnary equalityGateCont
      exact
        ⟨sourceFiberUnary, ledgerReadUnary, equalityGateUnary, sourceFiberCont,
          ledgerReadCont, equalityGateCont, hsame_refl V⟩

end BEDC.Derived.DigestProvenancePacketUp
