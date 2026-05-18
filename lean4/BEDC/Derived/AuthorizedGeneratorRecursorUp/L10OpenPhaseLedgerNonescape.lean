import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOpenPhaseLedgerNonescape [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead boundaryRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O A outputRead →
        Cont G N boundaryRead →
          Cont outputRead boundaryRead ledgerRead →
            PkgSig bundle ledgerRead pkg →
              UnaryHistory A ∧ UnaryHistory G ∧ UnaryHistory N ∧
                UnaryHistory outputRead ∧ UnaryHistory boundaryRead ∧
                  UnaryHistory ledgerRead ∧ Cont O A outputRead ∧
                    Cont G N boundaryRead ∧ Cont outputRead boundaryRead ledgerRead ∧
                      hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputRoute boundaryRoute ledgerRoute ledgerPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, provenanceUnary,
      boundaryUnary, nameUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary nameUnary boundaryRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed outputReadUnary boundaryReadUnary ledgerRoute
  exact
    ⟨auditUnary, boundaryUnary, nameUnary, outputReadUnary, boundaryReadUnary,
      ledgerReadUnary, outputRoute, boundaryRoute, ledgerRoute, transportAuditContinuation,
      provenancePkg, ledgerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
