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

theorem AuthorizedGeneratorRecursor_root_descent_audit_coupling [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert descentRead auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont descent audit descentRead ->
        Cont output audit auditRead ->
          Cont descentRead auditRead publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory descentRead ∧ UnaryHistory auditRead ∧ UnaryHistory publicRead ∧
                Cont descent audit descentRead ∧ Cont output audit auditRead ∧
                  Cont descentRead auditRead publicRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle publicRead pkg ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row descentRead ∨ hsame row auditRead ∨ hsame row publicRead)
                        (fun row : BHist => PkgSig bundle publicRead pkg ∧ hsame row publicRead)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier descentAuditRead outputAuditRead descentAuditPublic publicPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportSameAuditContinuation, provenancePkg⟩ := carrier
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed descentUnary auditUnary descentAuditRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed descentReadUnary auditReadUnary descentAuditPublic
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row descentRead ∨ hsame row auditRead ∨ hsame row publicRead)
        (fun row : BHist => PkgSig bundle publicRead pkg ∧ hsame row publicRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨publicPkg, source.left⟩
    }
  exact
    ⟨descentReadUnary, auditReadUnary, publicReadUnary, descentAuditRead, outputAuditRead,
      descentAuditPublic, provenancePkg, publicPkg, cert⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
