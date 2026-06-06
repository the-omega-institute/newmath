import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCarrier_candidate_boundary [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row kernel ∨ hsame row normalizer ∨ hsame row frontier ∨
              hsame row sn ∨ hsame row audit ∨ hsame row provenance)
          (fun row : BHist =>
            hsame row frontier ∧ Cont kernel normalizer frontier ∧
              PkgSig bundle provenance pkg)
          hsame ∧ UnaryHistory frontier ∧ Cont kernel normalizer frontier ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, _snUnary, _confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have sourceFrontier :
      (fun row : BHist => hsame row frontier ∧ UnaryHistory row) frontier := by
    exact ⟨hsame_refl frontier, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row kernel ∨ hsame row normalizer ∨ hsame row frontier ∨
              hsame row sn ∨ hsame row audit ∨ hsame row provenance)
          (fun row : BHist =>
            hsame row frontier ∧ Cont kernel normalizer frontier ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontier sourceFrontier
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
      exact Or.inr (Or.inr (Or.inl sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, kernelNormalizerFrontier, provenancePkg⟩
  }
  exact ⟨cert, frontierUnary, kernelNormalizerFrontier, provenancePkg⟩

end BEDC.Derived.MetacicNormalizationAuditUp
