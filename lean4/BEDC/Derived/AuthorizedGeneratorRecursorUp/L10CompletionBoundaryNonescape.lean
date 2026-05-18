import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorL10CompletionBoundaryNonescape [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert streamRead regSeqRead realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont output audit streamRead →
        Cont streamRead continuation regSeqRead →
          Cont regSeqRead boundary realRead →
            Cont realRead localCert completionRead →
              PkgSig bundle completionRead pkg →
                UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧ UnaryHistory realRead ∧
                  UnaryHistory completionRead ∧ Cont output audit streamRead ∧
                    Cont streamRead continuation regSeqRead ∧
                      Cont regSeqRead boundary realRead ∧ Cont realRead localCert completionRead ∧
                        hsame transport (append audit continuation) ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditStream streamContinuationRegSeq regSeqBoundaryReal
    realLocalCompletion completionPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed outputUnary auditUnary outputAuditStream
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed streamUnary continuationUnary streamContinuationRegSeq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqUnary boundaryUnary regSeqBoundaryReal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary localCertUnary realLocalCompletion
  exact
    ⟨streamUnary, regSeqUnary, realUnary, completionUnary, outputAuditStream,
      streamContinuationRegSeq, regSeqBoundaryReal, realLocalCompletion,
      transportAuditContinuation, provenancePkg, completionPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
