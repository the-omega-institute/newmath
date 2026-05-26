import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorL10OutputDownstreamCoverage
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      streamRead regseqRead realRead ledgerRead downstreamRead : BHist} :
    Cont output audit streamRead →
      Cont streamRead routes regseqRead →
        Cont regseqRead provenance realRead →
          Cont gap name ledgerRead →
            Cont realRead ledgerRead downstreamRead →
              UnaryHistory output →
                UnaryHistory audit →
                  UnaryHistory routes →
                    UnaryHistory provenance →
                      UnaryHistory gap →
                        UnaryHistory name →
                          UnaryHistory streamRead ∧ UnaryHistory regseqRead ∧
                            UnaryHistory realRead ∧ UnaryHistory ledgerRead ∧
                              UnaryHistory downstreamRead ∧ Cont output audit streamRead ∧
                                Cont streamRead routes regseqRead ∧
                                  Cont regseqRead provenance realRead ∧
                                    Cont gap name ledgerRead ∧
                                      Cont realRead ledgerRead downstreamRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro outputAuditStream streamRoutesRegseq regseqProvenanceReal gapNameLedger
    realLedgerDownstream outputUnary auditUnary routesUnary provenanceUnary gapUnary nameUnary
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed outputUnary auditUnary outputAuditStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary routesUnary streamRoutesRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary provenanceUnary regseqProvenanceReal
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed gapUnary nameUnary gapNameLedger
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed realUnary ledgerUnary realLedgerDownstream
  exact
    ⟨streamUnary, regseqUnary, realUnary, ledgerUnary, downstreamUnary, outputAuditStream,
      streamRoutesRegseq, regseqProvenanceReal, gapNameLedger, realLedgerDownstream⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
