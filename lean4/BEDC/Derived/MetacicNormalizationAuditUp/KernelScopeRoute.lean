import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditKernelScopeRoute [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg →
      Cont audit replay scopeRead →
        PkgSig bundle scopeRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row scopeRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
              (fun row : BHist =>
                hsame row kernel ∨ hsame row normalizer ∨ hsame row frontier ∨
                  hsame row sn ∨ hsame row audit ∨ hsame row scopeRead ∨
                    hsame row provenance ∨ hsame row localName)
              (fun row : BHist =>
                hsame row scopeRead ∧ Cont kernel normalizer frontier ∧
                  Cont frontier sn audit ∧ Cont audit replay scopeRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
              hsame ∧ UnaryHistory frontier ∧ UnaryHistory audit ∧
            UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory PkgSig
  intro carrier auditReplayScope scopePkg
  obtain ⟨kernelUnary, normalizerUnary, _frontierUnary, snUnary, _confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, kernelNormalizerFrontier, frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, localNamePkg⟩ := carrier
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed kernelUnary normalizerUnary kernelNormalizerFrontier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed auditUnary replayUnary auditReplayScope
  have sourceScope :
      (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        scopeRead :=
    ⟨hsame_refl scopeRead, scopeUnary, scopePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row ∧
            PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row kernel ∨ hsame row normalizer ∨ hsame row frontier ∨
              hsame row sn ∨ hsame row audit ∨ hsame row scopeRead ∨
                hsame row provenance ∨ hsame row localName)
          (fun row : BHist =>
            hsame row scopeRead ∧ Cont kernel normalizer frontier ∧
              Cont frontier sn audit ∧ Cont audit replay scopeRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead sourceScope
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
        intro _row other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, kernelNormalizerFrontier, frontierSnAudit, auditReplayScope,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, frontierUnary, auditUnary, scopeUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
