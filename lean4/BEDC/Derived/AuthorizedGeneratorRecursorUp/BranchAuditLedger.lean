import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBranchAuditLedger [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead auditRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont branch audit branchRead ->
        Cont branchRead continuation auditRead ->
          Cont auditRead localCert ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              UnaryHistory branchRead ∧ UnaryHistory auditRead ∧ UnaryHistory ledgerRead ∧
                Cont branch audit branchRead ∧ Cont branchRead continuation auditRead ∧
                  Cont auditRead localCert ledgerRead ∧
                    hsame transport (append audit continuation) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchAuditRead branchReadContinuationAudit auditReadLocalLedger ledgerPkg
  obtain
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, branchUnary, _descentUnary,
      _outputUnary, auditUnary, _transportUnary, continuationUnary, provenanceUnary,
      _boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ :=
      carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary auditUnary branchAuditRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed branchReadUnary continuationUnary branchReadContinuationAudit
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed auditReadUnary localCertUnary auditReadLocalLedger
  exact
    ⟨branchReadUnary, auditReadUnary, ledgerReadUnary, branchAuditRead,
      branchReadContinuationAudit, auditReadLocalLedger, transportAuditContinuation,
      provenancePkg, ledgerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
