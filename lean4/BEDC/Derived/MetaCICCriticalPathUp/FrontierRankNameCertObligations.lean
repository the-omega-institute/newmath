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

theorem MetaCICCriticalPathFrontierRankNameCertObligations [AskSetup] [PackageSetup]
    {openNode readyRank downstreamRank obstructionLedger replayRead provenance localName
      namecertRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg ->
      Cont replayRead localName namecertRead ->
        PkgSig bundle namecertRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                (hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                  hsame row obstructionLedger ∨ hsame row replayRead ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row namecertRead) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                  hsame row obstructionLedger ∨ hsame row replayRead ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row namecertRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle namecertRead pkg ∧ Cont replayRead localName namecertRead)
              hsame ∧
            UnaryHistory namecertRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontierRank namecertRoute namecertPkg
  obtain ⟨openUnary, readyUnary, downstreamUnary, obstructionUnary, replayUnary,
    provenanceUnary, localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have namecertUnary : UnaryHistory namecertRead :=
    unary_cont_closed replayUnary localNameUnary namecertRoute
  have sourceNamecert :
      (fun row : BHist =>
        (hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
          hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row provenance ∨
            hsame row localName ∨ hsame row namecertRead) ∧ UnaryHistory row)
          namecertRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hsame_refl namecertRead))))))), namecertUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row namecertRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row namecertRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle namecertRead pkg ∧ Cont replayRead localName namecertRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namecertRead sourceNamecert
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
                                  | inr sameNamecert =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inr (Or.inr
                                          (hsame_trans (hsame_symm sameRows)
                                            sameNamecert)))))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namecertPkg, namecertRoute⟩
  }
  exact ⟨cert, namecertUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
