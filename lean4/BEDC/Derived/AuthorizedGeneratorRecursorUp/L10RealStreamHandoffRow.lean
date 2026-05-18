import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRealStreamHandoffRow [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N streamRead regSeqRead realRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O A streamRead →
        Cont streamRead C regSeqRead →
          Cont regSeqRead G realRead →
            Cont realRead N handoff →
              PkgSig bundle handoff pkg →
                UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory G ∧
                  UnaryHistory N ∧ UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧
                    UnaryHistory realRead ∧ UnaryHistory handoff ∧ hsame H (append A C) ∧
                      Cont O A streamRead ∧ Cont streamRead C regSeqRead ∧
                        Cont regSeqRead G realRead ∧ Cont realRead N handoff ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditStream streamContinuationRegSeq regSeqBoundaryReal realNameHandoff
    handoffPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary, outputUnary,
      auditUnary, _transportUnary, continuationUnary, provenanceUnary, boundaryUnary, nameUnary,
      _signatureEliminatorMotive, _motiveBranchDescent, _descentOutputAudit,
      auditContinuationSame, provenancePkg⟩
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed outputUnary auditUnary outputAuditStream
  have regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed streamReadUnary continuationUnary streamContinuationRegSeq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqReadUnary boundaryUnary regSeqBoundaryReal
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed realReadUnary nameUnary realNameHandoff
  exact
    ⟨outputUnary, auditUnary, continuationUnary, boundaryUnary, nameUnary, streamReadUnary,
      regSeqReadUnary, realReadUnary, handoffUnary, auditContinuationSame, outputAuditStream,
      streamContinuationRegSeq, regSeqBoundaryReal, realNameHandoff, provenancePkg, handoffPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
