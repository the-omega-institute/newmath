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

theorem MetaCICCriticalPathDownstreamUnblockCoverage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName openNode readyRank downstreamRank obstructionLedger replayRead dependencyRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank obstructionLedger
          replayRead provenance localName bundle pkg →
        Cont localName readyRank dependencyRead →
          PkgSig bundle dependencyRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row dependencyRead ∨ hsame row localName) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                    hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row localName ∨
                      hsame row dependencyRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle dependencyRead pkg ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory dependencyRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro _packet frontierRank localReadyDependency dependencyPkg
  obtain ⟨_openUnary, readyUnary, _downstreamUnary, _obstructionUnary, _replayUnary,
    provenanceUnary, localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed localNameUnary readyUnary localReadyDependency
  have sourceDependency :
      (fun row : BHist =>
        (hsame row dependencyRead ∨ hsame row localName) ∧ UnaryHistory row)
          dependencyRead := by
    exact ⟨Or.inl (hsame_refl dependencyRead), dependencyUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dependencyRead ∨ hsame row localName) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row localName ∨
                hsame row dependencyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle dependencyRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dependencyRead sourceDependency
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
          | inl sameDependency =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDependency)
          | inr sameLocalName =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameLocalName)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameDependency =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameDependency)))))
      | inr sameLocalName =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameLocalName)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, dependencyPkg, provenancePkg⟩
  }
  exact ⟨cert, dependencyUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
