import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateResidualDiamondLock [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead residualRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead handoff residualRead →
          Cont residualRead obstruction socketRead →
            PkgSig bundle socketRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row candidateRead ∨ hsame row residualRead ∨
                      hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                        hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidateRead ∨ hsame row residualRead ∨
                      hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                        hsame row regseq ∨ hsame row realSeal)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle socketRead pkg)
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                  UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateHandoffResidual
    residualObstructionSocket socketPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffResidual
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionSocket
  have sourceAtSocket :
      (fun row : BHist =>
        (hsame row candidateRead ∨ hsame row residualRead ∨ hsame row socketRead ∨
          hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
            hsame row realSeal) ∧ UnaryHistory row) socketRead := by
    exact ⟨Or.inr (Or.inr (Or.inl (hsame_refl socketRead))), socketUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row residualRead ∨ hsame row socketRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row residualRead ∨ hsame row socketRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle socketRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceAtSocket
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
        intro row other sameRows source
        have patternOther :
            hsame other candidateRead ∨ hsame other residualRead ∨
              hsame other socketRead ∨ hsame other dyadic ∨ hsame other stream ∨
                hsame other regseq ∨ hsame other realSeal := by
          cases source.left with
          | inl rowCandidate =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) rowCandidate)
          | inr rest =>
              cases rest with
              | inl rowResidual =>
                  exact
                    Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowResidual))
              | inr rest =>
                  cases rest with
                  | inl rowSocket =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowSocket)))
                  | inr rest =>
                      cases rest with
                      | inl rowDyadic =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) rowDyadic))))
                      | inr rest =>
                          cases rest with
                          | inl rowStream =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans
                                            (hsame_symm sameRows) rowStream)))))
                          | inr rest =>
                              cases rest with
                              | inl rowRegseq =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans
                                                  (hsame_symm sameRows) rowRegseq))))))
                              | inr rowRealSeal =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (hsame_trans
                                                  (hsame_symm sameRows) rowRealSeal))))))
        exact ⟨patternOther, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketPkg⟩
  }
  exact ⟨cert, candidateUnary, residualUnary, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
