import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateMediatedSNConfluence [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName candidateRead closedRead residualRead confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg →
      Cont frontier sn candidateRead →
        Cont candidateRead audit closedRead →
          Cont closedRead replay residualRead →
            Cont residualRead confluence confluenceRead →
              PkgSig bundle confluenceRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row confluenceRead ∧ UnaryHistory row ∧
                        PkgSig bundle row pkg)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row closedRead ∨
                        hsame row residualRead ∨ hsame row confluenceRead ∨
                          hsame row provenance)
                    (fun row : BHist =>
                      hsame row confluenceRead ∧ Cont frontier sn candidateRead ∧
                        Cont candidateRead audit closedRead ∧
                          Cont closedRead replay residualRead ∧
                            Cont residualRead confluence confluenceRead ∧
                              PkgSig bundle provenance pkg)
                    hsame ∧ UnaryHistory candidateRead ∧ UnaryHistory closedRead ∧
                  UnaryHistory residualRead ∧ UnaryHistory confluenceRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frontierSnCandidate candidateAuditClosed closedReplayResidual
    residualConfluenceRead confluencePkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, confluenceUnary,
    auditUnary, _ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit,
    _confluenceAuditLedger, _transportReplaySame, provenancePkg, _localNamePkg⟩ :=
    carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed frontierUnary snUnary frontierSnCandidate
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed candidateUnary auditUnary candidateAuditClosed
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed closedUnary replayUnary closedReplayResidual
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed residualUnary confluenceUnary residualConfluenceRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row confluenceRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row closedRead ∨ hsame row residualRead ∨
              hsame row confluenceRead ∨ hsame row provenance)
          (fun row : BHist =>
            hsame row confluenceRead ∧ Cont frontier sn candidateRead ∧
              Cont candidateRead audit closedRead ∧ Cont closedRead replay residualRead ∧
                Cont residualRead confluence confluenceRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro confluenceRead
        ⟨hsame_refl confluenceRead, confluenceReadUnary, confluencePkg⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, frontierSnCandidate, candidateAuditClosed,
          closedReplayResidual, residualConfluenceRead, provenancePkg⟩
  }
  exact
    ⟨cert, candidateUnary, closedUnary, residualUnary, confluenceReadUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
