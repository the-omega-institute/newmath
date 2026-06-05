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

theorem MetaCICCriticalPathCandidateFrontierAxiomBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName candidateRead ->
        Cont candidateRead discharge frontierRead ->
          Cont frontierRead obstruction socketRead ->
            PkgSig bundle socketRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row candidateRead ∨ hsame row frontierRead ∨
                      hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                        hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidateRead ∨ hsame row frontierRead ∨
                      hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                        hsame row regseq ∨ hsame row realSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                      PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                  UnaryHistory socketRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro ledger continuationLocalNameCandidate candidateDischargeFrontier
    frontierObstructionSocket socketPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary dischargeUnary candidateDischargeFrontier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed frontierUnary obstructionUnary frontierObstructionSocket
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row socketRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row socketRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro candidateRead ⟨Or.inl (hsame_refl candidateRead), candidateUnary⟩
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
          | inl candidateSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) candidateSame)
          | inr rest =>
              cases rest with
              | inl frontierSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) frontierSame))
              | inr rest =>
                  cases rest with
                  | inl socketSame =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) socketSame)))
                  | inr rest =>
                      cases rest with
                      | inl dyadicSame =>
                          exact
                            Or.inr (Or.inr (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) dyadicSame))))
                      | inr rest =>
                          cases rest with
                          | inl streamSame =>
                              exact
                                Or.inr (Or.inr (Or.inr (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) streamSame)))))
                          | inr rest =>
                              cases rest with
                              | inl regseqSame =>
                                  exact
                                    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) regseqSame))))))
                              | inr realSealSame =>
                                  exact
                                    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                      (hsame_trans (hsame_symm sameRows) realSealSame))))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateUnary, frontierUnary, socketUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
