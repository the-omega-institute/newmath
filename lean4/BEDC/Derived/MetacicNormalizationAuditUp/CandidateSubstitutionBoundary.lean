import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateSubstitutionBoundary [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      candidateRead closedRead residualRead substitutionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg →
      Cont frontier sn candidateRead →
        Cont candidateRead audit closedRead →
          Cont closedRead replay residualRead →
            Cont residualRead ledger substitutionRead →
              PkgSig bundle substitutionRead pkg →
                SemanticNameCert
                  (fun row : BHist => hsame row substitutionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row frontier ∨ hsame row candidateRead ∨ hsame row closedRead ∨
                      hsame row residualRead ∨ hsame row substitutionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont frontier sn candidateRead ∧
                      Cont candidateRead audit closedRead ∧
                        Cont closedRead replay residualRead ∧
                          Cont residualRead ledger substitutionRead ∧
                            PkgSig bundle substitutionRead pkg)
                  hsame ∧ UnaryHistory candidateRead ∧ UnaryHistory closedRead ∧
                    UnaryHistory residualRead ∧ UnaryHistory substitutionRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frontierSnCandidate candidateAuditClosed closedReplayResidual
    residualLedgerSubstitution substitutionPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    auditUnary, ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, _provenancePkg, _localNamePkg⟩ := carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed frontierUnary snUnary frontierSnCandidate
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed candidateUnary auditUnary candidateAuditClosed
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed closedUnary replayUnary closedReplayResidual
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_cont_closed residualUnary ledgerUnary residualLedgerSubstitution
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row substitutionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row frontier ∨ hsame row candidateRead ∨ hsame row closedRead ∨
            hsame row residualRead ∨ hsame row substitutionRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont frontier sn candidateRead ∧
            Cont candidateRead audit closedRead ∧ Cont closedRead replay residualRead ∧
              Cont residualRead ledger substitutionRead ∧ PkgSig bundle substitutionRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro substitutionRead
        ⟨hsame_refl substitutionRead, substitutionUnary⟩
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
      exact
        ⟨sourceRow.right, frontierSnCandidate, candidateAuditClosed,
          closedReplayResidual, residualLedgerSubstitution, substitutionPkg⟩
  }
  exact ⟨cert, candidateUnary, closedUnary, residualUnary, substitutionUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
