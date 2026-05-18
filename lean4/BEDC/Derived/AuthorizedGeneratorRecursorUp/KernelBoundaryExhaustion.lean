import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorKernelBoundaryExhaustion [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert boundaryRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont boundary localCert boundaryRead ->
        Cont branch continuation publicRead ->
          UnaryHistory boundaryRead ∧ UnaryHistory publicRead ∧
            Cont signature eliminator motive ∧ Cont motive branch descent ∧
              Cont descent output audit ∧ Cont boundary localCert boundaryRead ∧
                Cont branch continuation publicRead ∧ hsame transport (append audit continuation) ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro carrier boundaryLocalCertRead branchContinuationPublicRead
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, branchUnary, _descentUnary,
    _outputUnary, _auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
    boundaryUnary, localCertUnary, signatureEliminatorMotive, motiveBranchDescent,
    descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary localCertUnary boundaryLocalCertRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchUnary continuationUnary branchContinuationPublicRead
  exact
    ⟨boundaryReadUnary, publicReadUnary, signatureEliminatorMotive, motiveBranchDescent,
      descentOutputAudit, boundaryLocalCertRead, branchContinuationPublicRead,
      transportAuditContinuation, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
