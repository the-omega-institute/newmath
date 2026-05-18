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

theorem AuthorizedGeneratorRecursorAuditRowCompleteness [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead auditBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead boundary auditBoundary ->
          PkgSig bundle auditBoundary pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row audit ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row audit ∧ Cont output audit outputRead ∧
                    Cont outputRead boundary auditBoundary)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle auditBoundary pkg ∧
                    hsame row audit)
                hsame ∧
              UnaryHistory audit ∧ UnaryHistory outputRead ∧ UnaryHistory auditBoundary ∧
                hsame transport (append audit continuation) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier outputAuditOutputRead outputBoundaryAuditBoundary auditBoundaryPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have auditBoundaryUnary : UnaryHistory auditBoundary :=
    unary_cont_closed outputReadUnary boundaryUnary outputBoundaryAuditBoundary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row audit ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row audit ∧ Cont output audit outputRead ∧
            Cont outputRead boundary auditBoundary)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle auditBoundary pkg ∧ hsame row audit)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro audit ⟨hsame_refl audit, auditUnary⟩
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
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, outputAuditOutputRead, outputBoundaryAuditBoundary⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, auditBoundaryPkg, source.left⟩
    }
  exact
    ⟨cert, auditUnary, outputReadUnary, auditBoundaryUnary, transportAuditContinuation⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
