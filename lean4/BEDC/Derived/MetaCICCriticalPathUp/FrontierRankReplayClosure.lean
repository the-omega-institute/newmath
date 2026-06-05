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

theorem MetaCICCriticalPathFrontierRankReplayClosure [AskSetup] [PackageSetup]
    {openNode readyRank downstreamRank obstructionLedger replayRead provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            (hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row localName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
              Cont obstructionLedger replayRead localName)
          hsame ∧
        UnaryHistory localName := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontierRank
  obtain ⟨_openUnary, _readyUnary, _downstreamUnary, obstructionUnary, replayUnary,
    _provenanceUnary, localNameUnary, _openReadyDownstream, obstructionReplayLocal,
    provenancePkg, localNamePkg⟩ := frontierRank
  have sourceLocalName :
      (fun row : BHist =>
        (hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row localName) ∧
          UnaryHistory row) localName := by
    exact ⟨Or.inr (Or.inr (hsame_refl localName)), localNameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row localName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
              Cont obstructionLedger replayRead localName)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocalName
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
          | inl sameObstruction =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameObstruction)
          | inr rest =>
              cases rest with
              | inl sameReplay =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameReplay))
              | inr sameLocalName =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameLocalName))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameObstruction =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameObstruction)))
      | inr rest =>
          cases rest with
          | inl sameReplay =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameReplay))))
          | inr sameLocalName =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameLocalName))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg, obstructionReplayLocal⟩
  }
  exact ⟨cert, localNameUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
