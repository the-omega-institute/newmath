import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorLedgerNonescapeSurface [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit auditRead ->
        Cont auditRead continuation publicRead ->
          UnaryHistory signature ∧ UnaryHistory branch ∧ UnaryHistory descent ∧
            UnaryHistory output ∧ UnaryHistory audit ∧ UnaryHistory auditRead ∧
              UnaryHistory publicRead ∧ hsame transport (append audit continuation) ∧
                Cont output audit auditRead ∧ Cont auditRead continuation publicRead ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier outputAuditRead auditContinuationPublic
  obtain ⟨signatureUnary, _eliminatorUnary, _motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed auditReadUnary continuationUnary auditContinuationPublic
  exact
    ⟨signatureUnary, branchUnary, descentUnary, outputUnary, auditUnary, auditReadUnary,
      publicReadUnary, transportAuditContinuation, outputAuditRead, auditContinuationPublic,
      provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
