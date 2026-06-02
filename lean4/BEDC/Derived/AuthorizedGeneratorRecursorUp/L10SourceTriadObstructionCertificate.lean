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

theorem AuthorizedGeneratorRecursorL10SourceTriadObstructionCertificate
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N sourceRead ledgerRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O N sourceRead ->
        Cont A G ledgerRead ->
          Cont sourceRead ledgerRead obstructionRead ->
            PkgSig bundle obstructionRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row O ∨ hsame row A ∨ hsame row G ∨ hsame row N ∨
                      hsame row obstructionRead)
                  (fun row : BHist =>
                    hsame row obstructionRead ∧ PkgSig bundle obstructionRead pkg)
                  hsame ∧
                UnaryHistory obstructionRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier outputLocalSource auditBoundaryLedger sourceLedgerObstruction obstructionPkg
  rcases carrier with
    ⟨_IUnary, _EUnary, _MUnary, _BUnary, _DUnary, outputUnary, auditUnary,
      _transportUnary, _continuationUnary, _provenanceUnary, boundaryUnary, localCertUnary,
      _signatureEliminatorMotive, _motiveBranchDescent, _descentOutputAudit,
      _transportAuditContinuation, provenancePkg⟩
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed outputUnary localCertUnary outputLocalSource
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed auditUnary boundaryUnary auditBoundaryLedger
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed sourceUnary ledgerUnary sourceLedgerObstruction
  have sourceObstruction :
      (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
        obstructionRead := by
    exact ⟨hsame_refl obstructionRead, obstructionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row A ∨ hsame row G ∨ hsame row N ∨
              hsame row obstructionRead)
          (fun row : BHist =>
            hsame row obstructionRead ∧ PkgSig bundle obstructionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obstructionRead sourceObstruction
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
        exact
          ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, obstructionPkg⟩
  }
  exact ⟨cert, obstructionUnary, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
