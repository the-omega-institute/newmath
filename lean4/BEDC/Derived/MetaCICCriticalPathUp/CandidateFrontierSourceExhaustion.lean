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

theorem MetaCICCriticalPathCandidateFrontierSourceExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead discharge frontierRead →
          Cont frontierRead obstruction socketRead →
            PkgSig bundle socketRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row socketRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row socketRead)
                  (fun _row : BHist =>
                    UnaryHistory socketRead ∧ PkgSig bundle socketRead pkg ∧
                      PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalCandidate candidateDischargeFrontier
    frontierObstructionSocket socketPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
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
  have sourceSocket :
      (fun row : BHist =>
        (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
          hsame row realSeal ∨ hsame row socketRead) ∧ UnaryHistory row) socketRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl socketRead)))), socketUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row socketRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row socketRead)
          (fun _row : BHist =>
            UnaryHistory socketRead ∧ PkgSig bundle socketRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocket
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
          | inl sameDyadic =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)
          | inr rest =>
              cases rest with
              | inl sameStream =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameStream))
              | inr rest =>
                  cases rest with
                  | inl sameRegseq =>
                      exact
                        Or.inr (Or.inr (Or.inl
                          (hsame_trans (hsame_symm sameRows) sameRegseq)))
                  | inr rest =>
                      cases rest with
                      | inl sameRealSeal =>
                          exact
                            Or.inr (Or.inr (Or.inr (Or.inl
                              (hsame_trans (hsame_symm sameRows) sameRealSeal))))
                      | inr sameSocket =>
                          exact
                            Or.inr (Or.inr (Or.inr (Or.inr
                              (hsame_trans (hsame_symm sameRows) sameSocket))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row _source
      exact ⟨socketUnary, socketPkg, realSealPkg⟩
  }
  exact ⟨cert, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
