import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRealSealRouteNonescape [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert streamRead regSeqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont output audit streamRead →
        Cont streamRead continuation regSeqRead →
          Cont regSeqRead boundary realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory output ∧ UnaryHistory audit ∧ UnaryHistory continuation ∧
                UnaryHistory boundary ∧ UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧
                  UnaryHistory realRead ∧ Cont output audit streamRead ∧
                    Cont streamRead continuation regSeqRead ∧ Cont regSeqRead boundary realRead ∧
                      hsame transport (append audit continuation) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditStream streamContinuationRegSeq regSeqBoundaryReal realPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed outputUnary auditUnary outputAuditStream
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed streamUnary continuationUnary streamContinuationRegSeq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqUnary boundaryUnary regSeqBoundaryReal
  exact
    ⟨outputUnary, auditUnary, continuationUnary, boundaryUnary, streamUnary, regSeqUnary,
      realUnary, outputAuditStream, streamContinuationRegSeq, regSeqBoundaryReal,
      transportAuditContinuation, provenancePkg, realPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
