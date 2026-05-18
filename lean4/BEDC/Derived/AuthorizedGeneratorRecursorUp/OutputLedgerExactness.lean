import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOutputLedgerExactness [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O A outputRead →
        Cont outputRead C publicRead →
          PkgSig bundle publicRead pkg →
            UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory outputRead ∧
              UnaryHistory publicRead ∧ Cont O A outputRead ∧
                Cont outputRead C publicRead ∧ hsame H (append A C) ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditRead outputContinuationPublic publicPkg
  obtain ⟨_inputUnary, _elimUnary, _motiveUnary, _branchUnary, _descentUnary, outputUnary,
    auditUnary, _transportUnary, continuationUnary, _provenanceUnary, _boundaryUnary,
    _localCertUnary, _inputElimMotive, _motiveBranchDescent, _descentOutputAudit,
    transportAuditContinuation, provenancePkg⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary continuationUnary outputContinuationPublic
  exact
    ⟨outputUnary, auditUnary, outputReadUnary, publicReadUnary, outputAuditRead,
      outputContinuationPublic, transportAuditContinuation, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
