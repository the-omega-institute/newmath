import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_closed_substitution_budget_lock
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead closedRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont descent output outputRead ->
        Cont outputRead boundary closedRead ->
          Cont closedRead localCert budgetRead ->
            PkgSig bundle budgetRead pkg ->
              UnaryHistory outputRead ∧ UnaryHistory closedRead ∧ UnaryHistory budgetRead ∧
                Cont descent output outputRead ∧ Cont outputRead boundary closedRead ∧
                  Cont closedRead localCert budgetRead ∧
                    hsame transport (append audit continuation) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier descentOutputRead outputBoundaryClosed closedLocalBudget budgetPkg
  obtain
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, descentUnary,
      outputUnary, _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ :=
      carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary descentOutputRead
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed outputReadUnary boundaryUnary outputBoundaryClosed
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed closedReadUnary localCertUnary closedLocalBudget
  exact
    ⟨outputReadUnary, closedReadUnary, budgetReadUnary, descentOutputRead,
      outputBoundaryClosed, closedLocalBudget, transportAuditContinuation, provenancePkg,
      budgetPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
