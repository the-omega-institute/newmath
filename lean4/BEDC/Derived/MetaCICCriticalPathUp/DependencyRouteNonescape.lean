import BEDC.Derived.MetaCICCriticalPathUp.FrontierRankOpenNode

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathFrontierRank_dependency_route_nonescape
    [AskSetup] [PackageSetup]
    {openNode readyRank downstreamRank obstructionLedger replayRead provenance localName
      dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg →
      Cont obstructionLedger replayRead dependencyRead →
        PkgSig bundle dependencyRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row readyRank ∨ hsame row obstructionLedger ∨ hsame row replayRead ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row dependencyRead) ∧
                    UnaryHistory row)
              (fun row : BHist =>
                hsame row readyRank ∨ hsame row obstructionLedger ∨ hsame row replayRead ∨
                  hsame row provenance ∨ hsame row localName ∨
                    Cont obstructionLedger replayRead dependencyRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle dependencyRead pkg ∧
                    Cont obstructionLedger replayRead dependencyRead)
              hsame ∧
            UnaryHistory dependencyRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontierRank dependencyRoute dependencyPkg
  obtain ⟨_openUnary, readyUnary, _downstreamUnary, obstructionUnary, replayUnary,
    provenanceUnary, _localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed obstructionUnary replayUnary dependencyRoute
  have sourceReady :
      (fun row : BHist =>
        (hsame row readyRank ∨ hsame row obstructionLedger ∨ hsame row replayRead ∨
          hsame row provenance ∨ hsame row localName ∨ hsame row dependencyRead) ∧
            UnaryHistory row) readyRank := by
    exact ⟨Or.inl (hsame_refl readyRank), readyUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row readyRank ∨ hsame row obstructionLedger ∨ hsame row replayRead ∨
              hsame row provenance ∨ hsame row localName ∨ hsame row dependencyRead) ∧
                UnaryHistory row)
          (fun row : BHist =>
            hsame row readyRank ∨ hsame row obstructionLedger ∨ hsame row replayRead ∨
              hsame row provenance ∨ hsame row localName ∨
                Cont obstructionLedger replayRead dependencyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle dependencyRead pkg ∧
                Cont obstructionLedger replayRead dependencyRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readyRank sourceReady
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
          | inl readySame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) readySame)
          | inr rest =>
              cases rest with
              | inl obstructionSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) obstructionSame))
              | inr rest =>
                  cases rest with
                  | inl replaySame =>
                      exact Or.inr (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) replaySame)))
                  | inr rest =>
                      cases rest with
                      | inl provenanceSame =>
                          exact Or.inr (Or.inr (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) provenanceSame))))
                      | inr rest =>
                          cases rest with
                          | inl localNameSame =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) localNameSame)))))
                          | inr dependencySame =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                (hsame_trans (hsame_symm sameRows) dependencySame)))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl readySame =>
          exact Or.inl readySame
      | inr rest =>
          cases rest with
          | inl obstructionSame =>
              exact Or.inr (Or.inl obstructionSame)
          | inr rest =>
              cases rest with
              | inl replaySame =>
                  exact Or.inr (Or.inr (Or.inl replaySame))
              | inr rest =>
                  cases rest with
                  | inl provenanceSame =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl provenanceSame)))
                  | inr rest =>
                      cases rest with
                      | inl localNameSame =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl localNameSame))))
                      | inr _dependencySame =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr dependencyRoute))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, dependencyPkg, dependencyRoute⟩
  }
  exact ⟨cert, dependencyUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
