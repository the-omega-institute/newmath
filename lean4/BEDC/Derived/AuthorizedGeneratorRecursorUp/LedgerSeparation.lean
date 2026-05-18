import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_ledger_separation [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert auditRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont audit continuation auditRead →
        Cont auditRead boundary ledgerRead →
          PkgSig bundle ledgerRead pkg →
            UnaryHistory auditRead ∧ UnaryHistory ledgerRead ∧
              hsame transport (append audit continuation) ∧
                Cont audit continuation auditRead ∧
                  Cont auditRead boundary ledgerRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame UnaryHistory
  intro carrier auditContinuationRead auditBoundaryLedger ledgerPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    _outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
    boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary continuationUnary auditContinuationRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed auditReadUnary boundaryUnary auditBoundaryLedger
  exact
    ⟨auditReadUnary, ledgerReadUnary, transportAuditContinuation, auditContinuationRead,
      auditBoundaryLedger, provenancePkg, ledgerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
