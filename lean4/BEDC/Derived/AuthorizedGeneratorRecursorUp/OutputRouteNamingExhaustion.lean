import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_output_route_naming_exhaustion
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead localCert namedRead ->
          PkgSig bundle namedRead pkg ->
            UnaryHistory output ∧ UnaryHistory audit ∧ UnaryHistory localCert ∧
              UnaryHistory outputRead ∧ UnaryHistory namedRead ∧
                Cont output audit outputRead ∧ Cont outputRead localCert namedRead ∧
                  hsame transport (append audit continuation) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditRead outputLocalNamed namedPkg
  obtain
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      _boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ :=
      carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed outputReadUnary localCertUnary outputLocalNamed
  exact
    ⟨outputUnary, auditUnary, localCertUnary, outputReadUnary, namedReadUnary,
      outputAuditRead, outputLocalNamed, transportAuditContinuation, provenancePkg, namedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
