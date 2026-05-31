import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorL10SourceTriadStrictObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N sourceRead ledgerRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O N sourceRead →
        Cont A G ledgerRead →
          Cont sourceRead ledgerRead obstructionRead →
            PkgSig bundle obstructionRead pkg →
              UnaryHistory sourceRead ∧ UnaryHistory ledgerRead ∧
                UnaryHistory obstructionRead ∧ Cont O N sourceRead ∧
                  Cont A G ledgerRead ∧ Cont sourceRead ledgerRead obstructionRead ∧
                    hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputLocalSource auditBoundaryLedger sourceLedgerObstruction obstructionPkg
  rcases carrier with
    ⟨_IUnary, _EUnary, _MUnary, _BUnary, _DUnary, outputUnary, auditUnary,
      _transportUnary, continuationUnary, _provenanceUnary, boundaryUnary, localCertUnary,
      _signatureEliminatorMotive, _motiveBranchDescent, _descentOutputAudit,
      transportAuditContinuation, provenancePkg⟩
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed outputUnary localCertUnary outputLocalSource
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed auditUnary boundaryUnary auditBoundaryLedger
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed sourceUnary ledgerUnary sourceLedgerObstruction
  exact
    ⟨sourceUnary, ledgerUnary, obstructionUnary, outputLocalSource, auditBoundaryLedger,
      sourceLedgerObstruction, transportAuditContinuation, provenancePkg, obstructionPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
