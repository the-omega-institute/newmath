import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAuditBranchSynchronization [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont branch descent branchRead ->
        Cont audit continuation auditRead ->
          Cont branchRead auditRead publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory branchRead ∧ UnaryHistory auditRead ∧ UnaryHistory publicRead ∧
                Cont motive branch descent ∧ Cont descent output audit ∧
                  Cont branch descent branchRead ∧ Cont audit continuation auditRead ∧
                    Cont branchRead auditRead publicRead ∧
                      hsame transport (append audit continuation) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchDescentRead auditContinuationRead branchAuditPublic publicPkg
  obtain
    ⟨_signatureUnary, _eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, _transportUnary, continuationUnary, _provenanceUnary, _boundaryUnary,
      _localCertUnary, _signatureEliminatorMotive, motiveBranchDescent, descentOutputAudit,
      transportAuditContinuation, provenancePkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchDescentRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary continuationUnary auditContinuationRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchReadUnary auditReadUnary branchAuditPublic
  exact
    ⟨branchReadUnary, auditReadUnary, publicReadUnary, motiveBranchDescent, descentOutputAudit,
      branchDescentRead, auditContinuationRead, branchAuditPublic, transportAuditContinuation,
      provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
