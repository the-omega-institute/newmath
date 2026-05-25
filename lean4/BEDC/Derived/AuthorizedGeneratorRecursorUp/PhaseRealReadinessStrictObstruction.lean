import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorPhaseRealReadinessStrictObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N streamRead regSeqRead realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A streamRead ->
        Cont streamRead C regSeqRead ->
          Cont regSeqRead G realRead ->
            Cont realRead N completionRead ->
              PkgSig bundle completionRead pkg ->
                UnaryHistory streamRead ∧ UnaryHistory regSeqRead ∧ UnaryHistory realRead ∧
                  UnaryHistory completionRead ∧ Cont O A streamRead ∧
                    Cont streamRead C regSeqRead ∧ Cont regSeqRead G realRead ∧
                      Cont realRead N completionRead ∧ hsame H (append A C) ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro carrier outputAuditStream streamContinuationRegSeq regSeqBoundaryReal realLocalCompletion
    completionPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, outputUnary, auditUnary,
      _transportUnary, continuationUnary, _provenanceUnary, boundaryUnary, localCertUnary,
      _signatureEliminatorMotive, _motiveBranchDescent, _descentOutputAudit,
      transportSame, provenancePkg⟩
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
      streamContinuationRegSeq, regSeqBoundaryReal, realLocalCompletion, transportSame,
      provenancePkg, completionPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
