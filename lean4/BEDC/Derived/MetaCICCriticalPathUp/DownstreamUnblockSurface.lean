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

theorem MetaCICCriticalPathDownstreamUnblockSurface [AskSetup] [PackageSetup]
    {openNode readyRank downstreamRank obstructionLedger replayRead provenance localName
      unblockRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank obstructionLedger
        replayRead provenance localName bundle pkg →
      Cont readyRank obstructionLedger unblockRead →
        PkgSig bundle unblockRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row unblockRead ∨ hsame row provenance ∨ hsame row localName) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                  hsame row obstructionLedger ∨ hsame row replayRead ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row unblockRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle unblockRead pkg ∧
                  PkgSig bundle provenance pkg ∧ Cont readyRank obstructionLedger unblockRead)
              hsame ∧
            UnaryHistory unblockRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontierRank readyObstructionUnblock unblockPkg
  obtain ⟨_openUnary, readyUnary, _downstreamUnary, obstructionUnary, _replayUnary,
    provenanceUnary, localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have unblockUnary : UnaryHistory unblockRead :=
    unary_cont_closed readyUnary obstructionUnary readyObstructionUnblock
  have sourceUnblock :
      (fun row : BHist =>
        (hsame row unblockRead ∨ hsame row provenance ∨ hsame row localName) ∧
          UnaryHistory row) unblockRead := by
    exact ⟨Or.inl (hsame_refl unblockRead), unblockUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row unblockRead ∨ hsame row provenance ∨ hsame row localName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row unblockRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle unblockRead pkg ∧
              PkgSig bundle provenance pkg ∧ Cont readyRank obstructionLedger unblockRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro unblockRead sourceUnblock
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
          | inl sameUnblock =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameUnblock)
          | inr rest =>
              cases rest with
              | inl sameProvenance =>
                  exact Or.inr (Or.inl
                    (hsame_trans (hsame_symm sameRows) sameProvenance))
              | inr sameLocalName =>
                  exact Or.inr (Or.inr
                    (hsame_trans (hsame_symm sameRows) sameLocalName))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameUnblock =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameUnblock))))))
      | inr rest =>
          cases rest with
          | inl sameProvenance =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameProvenance)))))
          | inr sameLocalName =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl sameLocalName))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, unblockPkg, provenancePkg, readyObstructionUnblock⟩
  }
  exact ⟨cert, unblockUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
