import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateFrontierExtension [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      frontierRead residualRead extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg ->
      Cont frontier sn frontierRead ->
        Cont frontierRead ledger residualRead ->
          Cont residualRead replay extensionRead ->
            PkgSig bundle extensionRead pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row frontier ∨ hsame row sn ∨ hsame row frontierRead ∨
                    hsame row ledger ∨ hsame row residualRead ∨ hsame row replay ∨
                      hsame row extensionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont frontier sn frontierRead ∧
                    Cont frontierRead ledger residualRead ∧
                      Cont residualRead replay extensionRead ∧
                        PkgSig bundle extensionRead pkg)
                hsame ∧ UnaryHistory frontierRead ∧ UnaryHistory residualRead ∧
                  UnaryHistory extensionRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frontierSnRead frontierLedgerResidual residualReplayExtension extensionPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    _auditUnary, ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, _provenancePkg, _localNamePkg⟩ := carrier
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed frontierUnary snUnary frontierSnRead
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierReadUnary ledgerUnary frontierLedgerResidual
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed residualUnary replayUnary residualReplayExtension
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row frontier ∨ hsame row sn ∨ hsame row frontierRead ∨
            hsame row ledger ∨ hsame row residualRead ∨ hsame row replay ∨
              hsame row extensionRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont frontier sn frontierRead ∧
            Cont frontierRead ledger residualRead ∧ Cont residualRead replay extensionRead ∧
              PkgSig bundle extensionRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro extensionRead
        ⟨hsame_refl extensionRead, extensionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, frontierSnRead, frontierLedgerResidual,
          residualReplayExtension, extensionPkg⟩
  }
  exact ⟨cert, frontierReadUnary, residualUnary, extensionUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
