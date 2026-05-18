import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorL10ConsumerReadbackTotality [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead continuation l10Read ->
          PkgSig bundle l10Read pkg ->
            UnaryHistory outputRead ∧ UnaryHistory l10Read ∧ Cont output audit outputRead ∧
              Cont outputRead continuation l10Read ∧ hsame transport (append audit continuation) ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle l10Read pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier outputAuditRead outputReadContinuationRead l10Pkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have l10ReadUnary : UnaryHistory l10Read :=
    unary_cont_closed outputReadUnary continuationUnary outputReadContinuationRead
  exact
    ⟨outputReadUnary, l10ReadUnary, outputAuditRead, outputReadContinuationRead,
      transportAuditContinuation, provenancePkg, l10Pkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
