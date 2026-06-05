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

theorem MetaCICCriticalPathCandidateMediatedSNResidualBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead residualRead
      socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead normalForm frontierRead →
          Cont frontierRead discharge residualRead →
            Cont residualRead obstruction socketRead →
              PkgSig bundle residualRead pkg →
                PkgSig bundle socketRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row candidateRead ∨ hsame row frontierRead ∨
                            hsame row residualRead ∨ hsame row socketRead ∨
                              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                                hsame row realSeal) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row frontierRead ∨
                          hsame row residualRead ∨ hsame row socketRead ∨
                            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                              hsame row realSeal)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle residualRead pkg ∧
                          PkgSig bundle socketRead pkg ∧ PkgSig bundle realSeal pkg)
                      hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                      UnaryHistory residualRead ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateNormalFrontier frontierDischargeResidual
    residualObstructionSocket residualPkg socketPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary normalFormUnary candidateNormalFrontier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierUnary dischargeUnary frontierDischargeResidual
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionSocket
  have sourceCandidate :
      (fun row : BHist =>
        (hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row residualRead ∨
            hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
              hsame row regseq ∨ hsame row realSeal) ∧
          UnaryHistory row) candidateRead := by
    exact ⟨Or.inl (hsame_refl candidateRead), candidateUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row residualRead ∨
                hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                  hsame row regseq ∨ hsame row realSeal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row residualRead ∨
              hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle residualRead pkg ∧
              PkgSig bundle socketRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro candidateRead sourceCandidate
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
          | inl sameCandidate =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate)
          | inr rest =>
              cases rest with
              | inl sameFrontier =>
                  exact Or.inr
                    (Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier))
              | inr rest =>
                  cases rest with
                  | inl sameResidual =>
                      exact Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameResidual)))
                  | inr rest =>
                      cases rest with
                      | inl sameSocket =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameSocket))))
                      | inr rest =>
                          cases rest with
                          | inl sameDyadic =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          sameDyadic)))))
                          | inr rest =>
                              cases rest with
                              | inl sameStream =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameStream))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameRegseq =>
                                      exact Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameRegseq)))))))
                                  | inr sameRealSeal =>
                                      exact Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameRealSeal)))))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, residualPkg, socketPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateUnary, frontierUnary, residualUnary, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
