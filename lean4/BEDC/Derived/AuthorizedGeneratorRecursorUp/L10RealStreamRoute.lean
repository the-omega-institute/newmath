import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_real_stream_route
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      streamRead regSeqRead realRead : BHist} :
    Cont output audit streamRead →
      Cont streamRead routes regSeqRead →
        Cont regSeqRead gap realRead →
          UnaryHistory output →
            UnaryHistory audit →
              UnaryHistory routes →
                UnaryHistory gap →
                  authorizedGeneratorRecursorFromEventFlow
                      (authorizedGeneratorRecursorToEventFlow
                        (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                          descent output audit transport routes provenance gap name)) =
                    some
                      (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent
                        output audit transport routes provenance gap name) ∧
                    UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧
                      UnaryHistory realRead ∧ Cont output audit streamRead ∧
                        Cont streamRead routes regSeqRead ∧
                          Cont regSeqRead gap realRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro outputAuditStream streamRoutesRegSeq regSeqGapReal outputUnary auditUnary routesUnary
    gapUnary
  have roundTrip :
      authorizedGeneratorRecursorFromEventFlow
          (authorizedGeneratorRecursorToEventFlow
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
            audit transport routes provenance gap name) :=
    AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment.right.left
      (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
        transport routes provenance gap name)
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed outputUnary auditUnary outputAuditStream
  have regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed streamReadUnary routesUnary streamRoutesRegSeq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqReadUnary gapUnary regSeqGapReal
  exact
    ⟨roundTrip, streamReadUnary, regSeqReadUnary, realReadUnary, outputAuditStream,
      streamRoutesRegSeq, regSeqGapReal⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
