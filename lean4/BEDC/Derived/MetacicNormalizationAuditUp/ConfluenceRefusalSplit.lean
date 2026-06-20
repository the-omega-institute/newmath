import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived
namespace MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditConfluenceRefusalSplit [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName candidateRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg ->
      Cont frontier sn candidateRead ->
        Cont confluence audit refusalRead ->
          PkgSig bundle provenance pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row kernel ∨ hsame row normalizer ∨ hsame row frontier ∨
                    hsame row sn ∨ hsame row confluence ∨ hsame row audit ∨
                      hsame row refusalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont frontier sn candidateRead ∧
                    Cont confluence audit refusalRead ∧ PkgSig bundle provenance pkg)
                hsame ∧ UnaryHistory candidateRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier frontierSnCandidate confluenceAuditRefusal provenancePkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, confluenceUnary,
    auditUnary, _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit,
    _confluenceAuditLedger, _transportReplaySame, _carrierProvenancePkg,
    _localNamePkg⟩ := carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed frontierUnary snUnary frontierSnCandidate
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed confluenceUnary auditUnary confluenceAuditRefusal
  have sourceRefusal :
      (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row) refusalRead := by
    exact ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row kernel ∨ hsame row normalizer ∨ hsame row frontier ∨ hsame row sn ∨
              hsame row confluence ∨ hsame row audit ∨ hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont frontier sn candidateRead ∧
              Cont confluence audit refusalRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceRefusal
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
        ⟨sourceRow.right, frontierSnCandidate, confluenceAuditRefusal,
          provenancePkg⟩
  }
  exact ⟨cert, candidateUnary, refusalUnary⟩

end MetacicNormalizationAuditUp
end BEDC.Derived
