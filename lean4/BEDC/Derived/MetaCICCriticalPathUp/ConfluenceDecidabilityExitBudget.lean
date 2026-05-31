import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathConfluenceDecidabilityExitBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead confluenceRead
      deciderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead dyadic confluenceRead →
          Cont confluenceRead stream deciderRead →
            PkgSig bundle deciderRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row candidateRead ∨ hsame row confluenceRead ∨
                        hsame row deciderRead ∨ hsame row dyadic ∨ hsame row stream ∨
                          hsame row regseq ∨ hsame row realSeal) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidateRead ∨ hsame row confluenceRead ∨
                      hsame row deciderRead ∨ hsame row dyadic ∨ hsame row stream ∨
                        hsame row regseq ∨ hsame row realSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle deciderRead pkg ∧
                      PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory confluenceRead ∧ UnaryHistory deciderRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateDyadicConfluence
    confluenceStreamDecider deciderPkg
  obtain ⟨packet, dyadicUnary, streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed candidateUnary dyadicUnary candidateDyadicConfluence
  have deciderUnary : UnaryHistory deciderRead :=
    unary_cont_closed confluenceUnary streamUnary confluenceStreamDecider
  have deciderSource :
      (fun row : BHist =>
        (hsame row candidateRead ∨ hsame row confluenceRead ∨ hsame row deciderRead ∨
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal) ∧
          UnaryHistory row) deciderRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inl (hsame_refl deciderRead))), deciderUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row confluenceRead ∨ hsame row deciderRead ∨
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row confluenceRead ∨ hsame row deciderRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle deciderRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro deciderRead deciderSource
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
        exact
          ⟨by
            cases source.left with
            | inl sameCandidate =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate)
            | inr rest =>
                cases rest with
                | inl sameConfluence =>
                    exact Or.inr (Or.inl
                      (hsame_trans (hsame_symm sameRows) sameConfluence))
                | inr rest =>
                    cases rest with
                    | inl sameDecider =>
                        exact Or.inr (Or.inr (Or.inl
                          (hsame_trans (hsame_symm sameRows) sameDecider)))
                    | inr rest =>
                        cases rest with
                        | inl sameDyadic =>
                            exact Or.inr (Or.inr (Or.inr (Or.inl
                              (hsame_trans (hsame_symm sameRows) sameDyadic))))
                        | inr rest =>
                            cases rest with
                            | inl sameStream =>
                                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameStream)))))
                            | inr rest =>
                                cases rest with
                                | inl sameRegseq =>
                                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                                      (hsame_trans (hsame_symm sameRows) sameRegseq))))))
                                | inr sameRealSeal =>
                                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                      (hsame_trans (hsame_symm sameRows) sameRealSeal))))))
            ,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, deciderPkg, realSealPkg⟩
  }
  exact ⟨cert, confluenceUnary, deciderUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
