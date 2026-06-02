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

theorem MetaCICCriticalPathCandidateMediatedSNPublicHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead socketRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead discharge frontierRead →
          Cont frontierRead obstruction socketRead →
            Cont socketRead realSeal publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row candidateRead ∨ hsame row frontierRead ∨
                        hsame row socketRead ∨ hsame row publicRead ∨
                          hsame row realSeal) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                        hsame row unblock ∨ hsame row discharge ∨ hsame row handoff ∨
                          hsame row continuation ∨ hsame row dyadic ∨ hsame row stream ∨
                            hsame row regseq ∨ hsame row realSeal ∨
                              hsame row candidateRead ∨ hsame row frontierRead ∨
                                hsame row socketRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
                        PkgSig bundle realSeal pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                    UnaryHistory socketRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro ledger continuationLocalCandidate candidateDischargeFrontier
    frontierObstructionSocket socketRealSealPublic publicPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary dischargeUnary candidateDischargeFrontier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed frontierUnary obstructionUnary frontierObstructionSocket
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed socketUnary realSealUnary socketRealSealPublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row socketRead ∨
              hsame row publicRead ∨ hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row unblock ∨ hsame row discharge ∨ hsame row handoff ∨
                hsame row continuation ∨ hsame row dyadic ∨ hsame row stream ∨
                  hsame row regseq ∨ hsame row realSeal ∨ hsame row candidateRead ∨
                    hsame row frontierRead ∨ hsame row socketRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead
          ⟨Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl publicRead)))), publicUnary⟩
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
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier))
              | inr rest =>
                  cases rest with
                  | inl sameSocket =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSocket)))
                  | inr rest =>
                      cases rest with
                      | inl samePublic =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) samePublic))))
                      | inr sameRealSeal =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (hsame_trans (hsame_symm sameRows) sameRealSeal))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCandidate =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inl sameCandidate)))))))))))
      | inr rest =>
          cases rest with
          | inl sameFrontier =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inl sameFrontier))))))))))))
          | inr rest =>
              cases rest with
              | inl sameSocket =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr (Or.inl sameSocket)))))))))))))
              | inr rest =>
                  cases rest with
                  | inl samePublic =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr samePublic)))))))))))))
                  | inr sameRealSeal =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inl sameRealSeal))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateUnary, frontierUnary, socketUnary, publicUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
