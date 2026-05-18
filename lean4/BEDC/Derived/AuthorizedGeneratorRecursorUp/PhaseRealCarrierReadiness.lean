import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorPhaseRealCarrierReadiness [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert streamRead regSeqRead realRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit streamRead ->
        Cont streamRead continuation regSeqRead ->
          Cont regSeqRead boundary realRead ->
            Cont signature provenance sourceRead ->
              PkgSig bundle realRead pkg ->
                UnaryHistory signature ∧ UnaryHistory output ∧ UnaryHistory audit ∧
                  UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧ UnaryHistory realRead ∧
                    UnaryHistory sourceRead ∧ hsame transport (append audit continuation) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier outputAuditStream streamContinuationRegSeq regSeqBoundaryReal
    signatureProvenanceSource realPkg
  obtain ⟨signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    outputUnary, auditUnary, _transportUnary, continuationUnary, provenanceUnary,
    boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportSameAuditContinuation, provenancePkg⟩ := carrier
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed outputUnary auditUnary outputAuditStream
  have regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed streamReadUnary continuationUnary streamContinuationRegSeq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqReadUnary boundaryUnary regSeqBoundaryReal
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed signatureUnary provenanceUnary signatureProvenanceSource
  exact
    ⟨signatureUnary, outputUnary, auditUnary, streamReadUnary, regSeqReadUnary, realReadUnary,
      sourceReadUnary, transportSameAuditContinuation, provenancePkg, realPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
