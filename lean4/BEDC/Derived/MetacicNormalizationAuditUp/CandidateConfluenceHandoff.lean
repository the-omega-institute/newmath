import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateConfluenceHandoff [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName candidateRead closedRead residualRead socketRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      Cont frontier sn candidateRead →
        Cont candidateRead audit closedRead →
          Cont closedRead replay residualRead →
            Cont residualRead confluence socketRead →
              Cont socketRead ledger handoffRead →
                PkgSig bundle handoffRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row handoffRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row closedRead ∨
                          hsame row residualRead ∨ hsame row socketRead ∨
                            hsame row handoffRead ∨ hsame row provenance)
                      (fun row : BHist =>
                        hsame row handoffRead ∧ Cont residualRead confluence socketRead ∧
                          Cont socketRead ledger handoffRead ∧
                            PkgSig bundle provenance pkg)
                      hsame ∧ UnaryHistory candidateRead ∧ UnaryHistory closedRead ∧
                    UnaryHistory residualRead ∧ UnaryHistory socketRead ∧
                      UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frontierSnCandidate candidateAuditClosed closedReplayResidual
    residualConfluenceSocket socketLedgerHandoff handoffPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, confluenceUnary,
    auditUnary, ledgerUnary, _transportUnary, replayUnary, provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit,
    _confluenceAuditLedger, _transportReplaySame, provenancePkg, _localNamePkg⟩ :=
    carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed frontierUnary snUnary frontierSnCandidate
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed candidateUnary auditUnary candidateAuditClosed
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed closedUnary replayUnary closedReplayResidual
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed residualUnary confluenceUnary residualConfluenceSocket
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed socketUnary ledgerUnary socketLedgerHandoff
  have sourceHandoff :
      (fun row : BHist =>
        hsame row handoffRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffUnary, handoffPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row handoffRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row closedRead ∨ hsame row residualRead ∨
              hsame row socketRead ∨ hsame row handoffRead ∨ hsame row provenance)
          (fun row : BHist =>
            hsame row handoffRead ∧ Cont residualRead confluence socketRead ∧
              Cont socketRead ledger handoffRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
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
        ⟨source.left, residualConfluenceSocket, socketLedgerHandoff, provenancePkg⟩
  }
  exact
    ⟨cert, candidateUnary, closedUnary, residualUnary, socketUnary, handoffUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
