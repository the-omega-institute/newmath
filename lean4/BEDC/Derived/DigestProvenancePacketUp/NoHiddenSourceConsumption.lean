import BEDC.Derived.DigestProvenancePacketUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.DigestProvenancePacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DigestProvenancePacketCarrier_no_hidden_source_consumption
    (R : DigestProvenancePacketUp) :
    ∃ V S F G E H C P N : BHist,
      R = DigestProvenancePacketUp.mk V S F G E H C P N ∧
        ∀ sourceFiber fiberGap gapExact exactTransport replayRead : BHist,
          Cont S F sourceFiber →
            Cont sourceFiber G fiberGap →
              Cont fiberGap E gapExact →
                Cont gapExact H exactTransport →
                  Cont exactTransport C replayRead →
                    UnaryHistory S →
                      UnaryHistory F →
                        UnaryHistory G →
                          UnaryHistory E →
                            UnaryHistory H →
                              UnaryHistory C →
                                UnaryHistory sourceFiber ∧ UnaryHistory fiberGap ∧
                                  UnaryHistory gapExact ∧ UnaryHistory exactTransport ∧
                                    UnaryHistory replayRead ∧ Cont S F sourceFiber ∧
                                      Cont sourceFiber G fiberGap ∧
                                        Cont fiberGap E gapExact ∧
                                          Cont gapExact H exactTransport ∧
                                            Cont exactTransport C replayRead ∧ hsame V V := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  cases R with
  | mk V S F G E H C P N =>
      refine ⟨V, S, F, G, E, H, C, P, N, rfl, ?_⟩
      intro sourceFiber fiberGap gapExact exactTransport replayRead sourceFiberCont
        fiberGapCont gapExactCont exactTransportCont replayReadCont sourceUnary fiberUnary
        gapUnary exactUnary transportUnary replayUnary
      have sourceFiberUnary : UnaryHistory sourceFiber :=
        unary_cont_closed sourceUnary fiberUnary sourceFiberCont
      have fiberGapUnary : UnaryHistory fiberGap :=
        unary_cont_closed sourceFiberUnary gapUnary fiberGapCont
      have gapExactUnary : UnaryHistory gapExact :=
        unary_cont_closed fiberGapUnary exactUnary gapExactCont
      have exactTransportUnary : UnaryHistory exactTransport :=
        unary_cont_closed gapExactUnary transportUnary exactTransportCont
      have replayReadUnary : UnaryHistory replayRead :=
        unary_cont_closed exactTransportUnary replayUnary replayReadCont
      exact
        ⟨sourceFiberUnary, fiberGapUnary, gapExactUnary, exactTransportUnary,
          replayReadUnary, sourceFiberCont, fiberGapCont, gapExactCont,
          exactTransportCont, replayReadCont, hsame_refl V⟩

end BEDC.Derived.DigestProvenancePacketUp
