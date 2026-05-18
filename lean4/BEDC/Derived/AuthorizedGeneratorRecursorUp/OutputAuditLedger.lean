import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOutputAuditLedger [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead auditedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead provenance auditedRead ->
          PkgSig bundle auditedRead pkg ->
            UnaryHistory output ∧ UnaryHistory audit ∧ UnaryHistory outputRead ∧
              UnaryHistory auditedRead ∧ hsame transport (append audit continuation) ∧
                Cont output audit outputRead ∧ Cont outputRead provenance auditedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle auditedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditRead outputProvenanceAudited auditedPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    outputUnary, auditUnary, _transportUnary, _continuationUnary, provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have auditedReadUnary : UnaryHistory auditedRead :=
    unary_cont_closed outputReadUnary provenanceUnary outputProvenanceAudited
  exact
    ⟨outputUnary, auditUnary, outputReadUnary, auditedReadUnary,
      transportAuditContinuation, outputAuditRead, outputProvenanceAudited, provenancePkg,
      auditedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
