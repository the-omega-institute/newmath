import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorPhaseRealLedgerNonescape [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont output localCert phaseRead →
        PkgSig bundle phaseRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output
                audit transport continuation provenance boundary localCert bundle pkg ∧
                  hsame row phaseRead)
            (fun row : BHist =>
              UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
                UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
                  UnaryHistory audit ∧ UnaryHistory phaseRead ∧ hsame row phaseRead)
            (fun _row : BHist =>
              Cont signature eliminator motive ∧ Cont motive branch descent ∧
                Cont descent output audit ∧ Cont output localCert phaseRead ∧
                  hsame transport (append audit continuation) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle phaseRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier outputLocalPhase phasePkg
  rcases carrier with
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, transportUnary, continuationUnary, provenanceUnary, boundaryUnary,
      localCertUnary, signatureEliminatorMotive, motiveBranchDescent, descentOutputAudit,
      transportAuditContinuation, provenancePkg⟩
  have retainedCarrier :
      AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg :=
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, transportUnary, continuationUnary, provenanceUnary, boundaryUnary,
      localCertUnary, signatureEliminatorMotive, motiveBranchDescent, descentOutputAudit,
      transportAuditContinuation, provenancePkg⟩
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed outputUnary localCertUnary outputLocalPhase
  have sourcePhase :
      (fun row : BHist =>
        AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
          transport continuation provenance boundary localCert bundle pkg ∧ hsame row phaseRead)
        phaseRead := by
    exact ⟨retainedCarrier, hsame_refl phaseRead⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro phaseRead sourcePhase
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
          auditUnary, phaseUnary, source.right⟩
    ledger_sound := by
      intro _row _source
      exact
        ⟨signatureEliminatorMotive, motiveBranchDescent, descentOutputAudit, outputLocalPhase,
          transportAuditContinuation, provenancePkg, phasePkg⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
