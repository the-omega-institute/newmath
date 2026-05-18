import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_output_route_audit_cover
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead transportRead auditedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead transport transportRead ->
          Cont transportRead localCert auditedRead ->
            PkgSig bundle auditedRead pkg ->
              UnaryHistory outputRead ∧ UnaryHistory transportRead ∧
                UnaryHistory auditedRead ∧ hsame transport (append audit continuation) ∧
                  Cont output audit outputRead ∧ Cont outputRead transport transportRead ∧
                    Cont transportRead localCert auditedRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle auditedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditOutputRead outputReadTransportTransportRead
    transportReadLocalCertAuditedRead auditedReadPkg
  obtain
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, transportUnary, _continuationUnary, _provenanceUnary,
      _boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ :=
      carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed outputReadUnary transportUnary outputReadTransportTransportRead
  have auditedReadUnary : UnaryHistory auditedRead :=
    unary_cont_closed transportReadUnary localCertUnary transportReadLocalCertAuditedRead
  exact
    ⟨outputReadUnary, transportReadUnary, auditedReadUnary, transportAuditContinuation,
      outputAuditOutputRead, outputReadTransportTransportRead, transportReadLocalCertAuditedRead,
      provenancePkg, auditedReadPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
