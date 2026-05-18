import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorPhaseRealRegSeqRatHandoff [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N streamSource regseqRead realEndpoint phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O H streamSource ->
        Cont streamSource C regseqRead ->
          Cont regseqRead G realEndpoint ->
            Cont realEndpoint N phaseRead ->
              PkgSig bundle phaseRead pkg ->
                UnaryHistory O ∧ UnaryHistory streamSource ∧ UnaryHistory regseqRead ∧
                  UnaryHistory realEndpoint ∧ UnaryHistory phaseRead ∧
                    Cont O H streamSource ∧ Cont streamSource C regseqRead ∧
                      Cont regseqRead G realEndpoint ∧ Cont realEndpoint N phaseRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle phaseRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputTransportStream streamContinuationRegseq regseqBoundaryReal
    realLocalPhase phasePkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, _auditUnary, transportUnary, continuationUnary, _provenanceUnary,
      boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, _transportAuditContinuation, provenancePkg⟩
  have streamUnary : UnaryHistory streamSource :=
    unary_cont_closed outputUnary transportUnary outputTransportStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary continuationUnary streamContinuationRegseq
  have realUnary : UnaryHistory realEndpoint :=
    unary_cont_closed regseqUnary boundaryUnary regseqBoundaryReal
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed realUnary localCertUnary realLocalPhase
  exact
    ⟨outputUnary, streamUnary, regseqUnary, realUnary, phaseUnary, outputTransportStream,
      streamContinuationRegseq, regseqBoundaryReal, realLocalPhase, provenancePkg, phasePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
