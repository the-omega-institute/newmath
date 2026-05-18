import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_closed_substitution_handoff
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead closedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont descent output outputRead ->
        Cont outputRead boundary closedRead ->
          PkgSig bundle closedRead pkg ->
            UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
              UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
                UnaryHistory audit ∧ UnaryHistory outputRead ∧ UnaryHistory closedRead ∧
                  Cont descent output outputRead ∧ Cont outputRead boundary closedRead ∧
                    hsame transport (append audit continuation) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle closedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier descentOutputRead outputReadBoundaryClosed closedPkg
  obtain
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, _transportUnary, _continuationUnary, _provenanceUnary, boundaryUnary,
      _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ :=
      carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary descentOutputRead
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed outputReadUnary boundaryUnary outputReadBoundaryClosed
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, outputReadUnary, closedReadUnary, descentOutputRead,
      outputReadBoundaryClosed, transportAuditContinuation, provenancePkg, closedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
