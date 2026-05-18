import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAuditLedgerNonescape [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont G N ledgerRead ->
        PkgSig bundle P pkg ->
          UnaryHistory A ∧ UnaryHistory G ∧ UnaryHistory N ∧ UnaryHistory ledgerRead ∧
            Cont G N ledgerRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier groundNameLedger provenancePkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    _outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportAuditContinuation, _provenancePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundaryUnary localCertUnary groundNameLedger
  exact
    ⟨auditUnary, boundaryUnary, localCertUnary, ledgerReadUnary, groundNameLedger,
      provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
