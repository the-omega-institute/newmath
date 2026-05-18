import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_root_audit_ledger_exactness [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead boundaryRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead C auditRead ->
          Cont auditRead G boundaryRead ->
            Cont boundaryRead N ledgerRead ->
              PkgSig bundle ledgerRead pkg ->
                UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory ledgerRead ∧
                    Cont O A outputRead ∧ Cont outputRead C auditRead ∧
                      Cont auditRead G boundaryRead ∧ Cont boundaryRead N ledgerRead ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditRead outputContinuationAudit auditBoundaryRead
    boundaryNameLedger ledgerPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    outputUnary, auditUnary, _transportUnary, continuationUnary, provenanceUnary,
    boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary continuationUnary outputContinuationAudit
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed auditReadUnary boundaryUnary auditBoundaryRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundaryReadUnary localCertUnary boundaryNameLedger
  exact
    ⟨outputReadUnary, auditReadUnary, boundaryReadUnary, ledgerReadUnary, outputAuditRead,
      outputContinuationAudit, auditBoundaryRead, boundaryNameLedger,
      transportAuditContinuation, provenancePkg, ledgerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
