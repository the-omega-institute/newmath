import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationAuditPublicCandidateConfluenceRefusal [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      publicRead confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg ->
      Cont audit replay publicRead ->
        Cont confluence audit confluenceRead ->
          PkgSig bundle publicRead pkg ->
            PkgSig bundle confluenceRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                      hsame row confluence ∨ hsame row publicRead)
                  (fun row : BHist =>
                    hsame row publicRead ∧ Cont audit replay publicRead ∧
                      Cont confluence audit confluenceRead ∧
                        PkgSig bundle provenance pkg)
                  hsame ∧ UnaryHistory publicRead ∧ UnaryHistory confluence := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier auditReplayPublic confluenceAuditRead publicPkg _confluencePkg
  obtain ⟨_kernelUnary, _normalizerUnary, _frontierUnary, _snUnary, confluenceUnary,
    auditUnary, _ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary replayUnary auditReplayPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
              hsame row confluence ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont audit replay publicRead ∧
              Cont confluence audit confluenceRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, auditReplayPublic, confluenceAuditRead, provenancePkg⟩
  }
  exact ⟨cert, publicUnary, confluenceUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
