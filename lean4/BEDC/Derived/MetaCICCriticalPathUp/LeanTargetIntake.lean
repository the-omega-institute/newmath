import BEDC.Derived.MetaCICCriticalPathUp.FrontierRankOpenNode

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathLeanTargetIntake [AskSetup] [PackageSetup]
    {openNode readyRank downstreamRank obstructionLedger replayRead provenance localName
      intakeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg →
      Cont readyRank localName intakeRead →
        PkgSig bundle intakeRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                  hsame row obstructionLedger ∨ hsame row replayRead ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row intakeRead) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                  hsame row obstructionLedger ∨ hsame row replayRead ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row intakeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle intakeRead pkg ∧ Cont readyRank localName intakeRead)
              hsame ∧
            UnaryHistory intakeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontierRank intakeRoute intakePkg
  obtain ⟨openUnary, readyUnary, downstreamUnary, obstructionUnary, replayUnary,
    provenanceUnary, localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have intakeUnary : UnaryHistory intakeRead :=
    unary_cont_closed readyUnary localNameUnary intakeRoute
  have sourceIntake :
      (fun row : BHist =>
        (hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
          hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row provenance ∨
            hsame row localName ∨ hsame row intakeRead) ∧ UnaryHistory row)
          intakeRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hsame_refl intakeRead))))))), intakeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row intakeRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row intakeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle intakeRead pkg ∧ Cont readyRank localName intakeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro intakeRead sourceIntake
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
          | inl sameOpen =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameOpen)
          | inr rest =>
              cases rest with
              | inl sameReady =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameReady))
              | inr rest =>
                  cases rest with
                  | inl sameDownstream =>
                      exact Or.inr (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameDownstream)))
                  | inr rest =>
                      cases rest with
                      | inl sameObstruction =>
                          exact Or.inr (Or.inr (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameObstruction))))
                      | inr rest =>
                          cases rest with
                          | inl sameReplay =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameReplay)))))
                          | inr rest =>
                              cases rest with
                              | inl sameProvenance =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows)
                                        sameProvenance))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameLocalName =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inr (Or.inl
                                          (hsame_trans (hsame_symm sameRows)
                                            sameLocalName)))))))
                                  | inr sameIntake =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inr (Or.inr
                                          (hsame_trans (hsame_symm sameRows)
                                            sameIntake)))))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, intakePkg, intakeRoute⟩
  }
  exact ⟨cert, intakeUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
