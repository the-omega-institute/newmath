import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_output_stability [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead outputRead' auditRead auditRead' publicRead publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont descent output outputRead ->
        Cont descent output outputRead' ->
          Cont outputRead audit auditRead ->
            Cont outputRead' audit auditRead' ->
              Cont auditRead continuation publicRead ->
                Cont auditRead' continuation publicRead' ->
                  PkgSig bundle provenance pkg ->
                    hsame outputRead outputRead' ∧ hsame auditRead auditRead' ∧
                      hsame publicRead publicRead' ∧ UnaryHistory publicRead ∧
                        UnaryHistory publicRead' ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier descentOutputRead descentOutputRead' outputAuditRead outputAuditRead'
    auditContinuationPublic auditContinuationPublic' _inputPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportAuditContinuation, provenancePkg⟩ := carrier
  have outputReadSame : hsame outputRead outputRead' :=
    cont_deterministic descentOutputRead descentOutputRead'
  have auditReadSame : hsame auditRead auditRead' :=
    cont_respects_hsame outputReadSame rfl outputAuditRead outputAuditRead'
  have publicReadSame : hsame publicRead publicRead' :=
    cont_respects_hsame auditReadSame rfl auditContinuationPublic auditContinuationPublic'
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary descentOutputRead
  have outputReadUnary' : UnaryHistory outputRead' :=
    unary_cont_closed descentUnary outputUnary descentOutputRead'
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary outputAuditRead
  have auditReadUnary' : UnaryHistory auditRead' :=
    unary_cont_closed outputReadUnary' auditUnary outputAuditRead'
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed auditReadUnary continuationUnary auditContinuationPublic
  have publicReadUnary' : UnaryHistory publicRead' :=
    unary_cont_closed auditReadUnary' continuationUnary auditContinuationPublic'
  exact
    ⟨outputReadSame, auditReadSame, publicReadSame, publicReadUnary, publicReadUnary',
      provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
