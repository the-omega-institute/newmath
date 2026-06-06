import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCarrier_public_route [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg ->
      Cont audit replay publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
              (fun row : BHist =>
                hsame row frontier ∨ hsame row sn ∨ hsame row confluence ∨
                  hsame row audit ∨ hsame row ledger ∨ hsame row publicRead ∨
                    hsame row provenance)
              (fun row : BHist =>
                hsame row publicRead ∧ Cont audit replay publicRead ∧
                  PkgSig bundle provenance pkg)
              hsame ∧ UnaryHistory audit ∧ UnaryHistory publicRead ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier auditReplayPublic publicPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary replayUnary auditReplayPublic
  have sourcePublic :
      (fun row : BHist =>
        hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary, publicPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row sn ∨ hsame row confluence ∨
              hsame row audit ∨ hsame row ledger ∨ hsame row publicRead ∨
                hsame row provenance)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont audit replay publicRead ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, auditReplayPublic, provenancePkg⟩
  }
  exact ⟨cert, auditUnary, publicUnary, provenancePkg⟩

end BEDC.Derived.MetacicNormalizationAuditUp
