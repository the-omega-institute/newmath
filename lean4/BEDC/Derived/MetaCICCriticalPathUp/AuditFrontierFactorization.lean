import BEDC.Derived.MetaCICCriticalPathUp.FrontierRankOpenNode
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathAuditFrontierFactorization [AskSetup] [PackageSetup]
    {openNode readyRank downstreamRank obstructionLedger replayRead provenance localName
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank obstructionLedger
        replayRead provenance localName bundle pkg →
      Cont openNode replayRead auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row auditRead ∨ hsame row openNode ∨ hsame row replayRead) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                  hsame row obstructionLedger ∨ hsame row replayRead ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row auditRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧
                  PkgSig bundle provenance pkg ∧ Cont openNode replayRead auditRead)
              hsame ∧
            UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontierRank openReplayAudit auditPkg
  obtain ⟨openUnary, _readyUnary, _downstreamUnary, _obstructionUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed openUnary replayUnary openReplayAudit
  have sourceAudit :
      (fun row : BHist =>
        (hsame row auditRead ∨ hsame row openNode ∨ hsame row replayRead) ∧
          UnaryHistory row) auditRead := by
    exact ⟨Or.inl (hsame_refl auditRead), auditUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row auditRead ∨ hsame row openNode ∨ hsame row replayRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧
              PkgSig bundle provenance pkg ∧ Cont openNode replayRead auditRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead sourceAudit
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
        constructor
        · cases source.left with
          | inl sameAudit =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameAudit)
          | inr rest =>
              cases rest with
              | inl sameOpen =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameOpen))
              | inr sameReplay =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameReplay))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameAudit =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameAudit))))))
      | inr rest =>
          cases rest with
          | inl sameOpen =>
              exact Or.inl sameOpen
          | inr sameReplay =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameReplay))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditPkg, provenancePkg, openReplayAudit⟩
  }
  exact ⟨cert, auditUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
