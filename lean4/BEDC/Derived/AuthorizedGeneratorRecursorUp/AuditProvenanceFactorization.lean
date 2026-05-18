import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_audit_provenance_factorization [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead continuation auditRead ->
          Cont auditRead localCert publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory output ∧ UnaryHistory audit ∧ UnaryHistory outputRead ∧
                UnaryHistory auditRead ∧ UnaryHistory publicRead ∧
                  Cont output audit outputRead ∧ Cont outputRead continuation auditRead ∧
                    Cont auditRead localCert publicRead ∧
                      hsame transport (append audit continuation) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditOutputRead outputReadContinuationAuditRead
    auditReadLocalCertPublicRead publicReadPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary continuationUnary outputReadContinuationAuditRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed auditReadUnary localCertUnary auditReadLocalCertPublicRead
  exact
    ⟨outputUnary, auditUnary, outputReadUnary, auditReadUnary, publicReadUnary,
      outputAuditOutputRead, outputReadContinuationAuditRead, auditReadLocalCertPublicRead,
      transportAuditContinuation, provenancePkg, publicReadPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
