import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_l10_source_row_admission
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      streamRead regSeqRead realRead sourceRead : BHist} :
    Cont output audit streamRead →
      Cont streamRead routes regSeqRead →
        Cont regSeqRead gap realRead →
          Cont signature provenance sourceRead →
            hsame transport transport →
              UnaryHistory output →
                UnaryHistory audit →
                  UnaryHistory routes →
                    UnaryHistory gap →
                      UnaryHistory signature →
                        UnaryHistory provenance →
                          authorizedGeneratorRecursorFromEventFlow
                              (authorizedGeneratorRecursorToEventFlow
                                (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                                  branches descent output audit transport routes provenance gap name)) =
                            some
                              (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                                descent output audit transport routes provenance gap name) ∧
                            UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧
                              UnaryHistory realRead ∧ UnaryHistory sourceRead ∧
                                Cont output audit streamRead ∧
                                  Cont streamRead routes regSeqRead ∧
                                    Cont regSeqRead gap realRead ∧
                                      Cont signature provenance sourceRead ∧
                                        hsame transport transport := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro outputAuditStream streamRoutesRegSeq regSeqGapReal signatureProvenanceSource
    transportSelf outputUnary auditUnary routesUnary gapUnary signatureUnary provenanceUnary
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
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed signatureUnary provenanceUnary signatureProvenanceSource
  exact
    ⟨roundTrip, streamReadUnary, regSeqReadUnary, realReadUnary, sourceReadUnary,
      outputAuditStream, streamRoutesRegSeq, regSeqGapReal, signatureProvenanceSource,
      transportSelf⟩

theorem AuthorizedGeneratorRecursorL10SourceAdmissionStrictObstruction
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      streamRead regSeqRead realRead sourceRead refusedRead : BHist} :
    Cont output audit streamRead →
      Cont streamRead routes regSeqRead →
        Cont regSeqRead gap realRead →
          Cont signature provenance sourceRead →
            Cont gap name refusedRead →
              hsame transport transport →
                UnaryHistory output →
                  UnaryHistory audit →
                    UnaryHistory routes →
                      UnaryHistory gap →
                        UnaryHistory signature →
                          UnaryHistory provenance →
                            UnaryHistory name →
                              authorizedGeneratorRecursorFromEventFlow
                                  (authorizedGeneratorRecursorToEventFlow
                                    (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                                      branches descent output audit transport routes provenance gap
                                      name)) =
                                some
                                  (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                                    branches descent output audit transport routes provenance gap
                                    name) ∧
                                UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧
                                  UnaryHistory realRead ∧ UnaryHistory sourceRead ∧
                                    UnaryHistory refusedRead ∧ Cont gap name refusedRead ∧
                                      hsame transport transport := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro outputAuditStream streamRoutesRegSeq regSeqGapReal signatureProvenanceSource
    gapNameRefused transportSelf outputUnary auditUnary routesUnary gapUnary signatureUnary
    provenanceUnary nameUnary
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
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed signatureUnary provenanceUnary signatureProvenanceSource
  have refusedReadUnary : UnaryHistory refusedRead :=
    unary_cont_closed gapUnary nameUnary gapNameRefused
  exact
    ⟨roundTrip, streamReadUnary, regSeqReadUnary, realReadUnary, sourceReadUnary,
      refusedReadUnary, gapNameRefused, transportSelf⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
