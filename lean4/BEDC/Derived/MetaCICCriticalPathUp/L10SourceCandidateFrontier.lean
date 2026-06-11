import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathL10SourceCandidateFrontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead handoff frontierRead →
          Cont frontierRead realSeal sourceRead →
            PkgSig bundle sourceRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row sourceRead ∨ hsame row dyadic ∨ hsame row stream ∨
                      hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidateRead ∨ hsame row frontierRead ∨
                      hsame row sourceRead ∨ hsame row dyadic ∨ hsame row stream ∨
                        hsame row regseq ∨ hsame row realSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle sourceRead pkg ∧
                      PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro ledger continuationLocalNameCandidate candidateHandoffFrontier
    frontierRealSealSource sourcePkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffFrontier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed frontierUnary realSealUnary frontierRealSealSource
  have sourceWitness :
      (fun row : BHist =>
        (hsame row sourceRead ∨ hsame row dyadic ∨ hsame row stream ∨
          hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row) sourceRead := by
    exact ⟨Or.inl (hsame_refl sourceRead), sourceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceRead ∨ hsame row dyadic ∨ hsame row stream ∨
              hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row sourceRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sourceRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceWitness
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
            | inl sameSource =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
            | inr rest =>
                cases rest with
                | inl sameDyadic =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic))
                | inr rest =>
                    cases rest with
                    | inl sameStream =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameStream)))
                    | inr rest =>
                        cases rest with
                        | inl sameRegseq =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows) sameRegseq))))
                        | inr sameRealSeal =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (hsame_trans (hsame_symm sameRows) sameRealSeal))))
            ,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact Or.inr (Or.inr (Or.inl sameSource))
      | inr rest =>
          cases rest with
          | inl sameDyadic =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameDyadic)))
          | inr rest =>
              cases rest with
              | inl sameStream =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameStream))))
              | inr rest =>
                  cases rest with
                  | inl sameRegseq =>
                      exact
                        Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRegseq)))))
                  | inr sameRealSeal =>
                      exact
                        Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameRealSeal)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourcePkg, realSealPkg⟩
  }
  exact ⟨cert, sourceUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
