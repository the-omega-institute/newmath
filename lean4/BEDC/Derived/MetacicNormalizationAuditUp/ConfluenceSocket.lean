import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditConfluenceSocket [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName residualRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg ->
      Cont audit replay residualRead ->
        Cont residualRead confluence socketRead ->
          PkgSig bundle socketRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row socketRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row audit ∨ hsame row replay ∨ hsame row residualRead ∨
                    hsame row confluence ∨ hsame row socketRead ∨ hsame row provenance)
                (fun row : BHist =>
                  hsame row socketRead ∧ Cont audit replay residualRead ∧
                    Cont residualRead confluence socketRead ∧ PkgSig bundle provenance pkg)
                hsame ∧ UnaryHistory residualRead ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier auditReplayResidual residualConfluenceSocket socketPkg
  obtain ⟨_kernelUnary, _normalizerUnary, _frontierUnary, _snUnary, confluenceUnary,
    auditUnary, _ledgerUnary, _transportUnary, replayUnary, provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed auditUnary replayUnary auditReplayResidual
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed residualUnary confluenceUnary residualConfluenceSocket
  have sourceSocket :
      (fun row : BHist =>
        hsame row socketRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg) socketRead := by
    exact ⟨hsame_refl socketRead, socketUnary, socketPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row socketRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row audit ∨ hsame row replay ∨ hsame row residualRead ∨
              hsame row confluence ∨ hsame row socketRead ∨ hsame row provenance)
          (fun row : BHist =>
            hsame row socketRead ∧ Cont audit replay residualRead ∧
              Cont residualRead confluence socketRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocket
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, auditReplayResidual, residualConfluenceSocket, provenancePkg⟩
  }
  exact ⟨cert, residualUnary, socketUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
