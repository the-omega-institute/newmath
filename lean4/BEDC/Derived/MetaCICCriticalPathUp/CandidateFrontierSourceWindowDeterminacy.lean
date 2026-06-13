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

theorem MetaCICCriticalPathCandidateFrontierSourceWindowDeterminacy
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead sourceWindowA
      sourceWindowB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead handoff frontierRead →
          hsame sourceWindowA frontierRead →
            hsame sourceWindowB frontierRead →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row sourceWindowA ∨ hsame row sourceWindowB ∨
                      hsame row frontierRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row candidateRead ∨
                        hsame row frontierRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont continuation localName candidateRead ∧
                      Cont candidateRead handoff frontierRead ∧ PkgSig bundle realSeal pkg)
                  hsame ∧
                hsame sourceWindowA sourceWindowB ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalCandidate candidateHandoffFrontier windowAFrontier
    windowBFrontier
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffFrontier
  have sourceFrontier :
      (fun row : BHist =>
        (hsame row sourceWindowA ∨ hsame row sourceWindowB ∨ hsame row frontierRead) ∧
          UnaryHistory row) frontierRead := by
    exact ⟨Or.inr (Or.inr (hsame_refl frontierRead)), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceWindowA ∨ hsame row sourceWindowB ∨
              hsame row frontierRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row candidateRead ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuation localName candidateRead ∧
              Cont candidateRead handoff frontierRead ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead sourceFrontier
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
          | inl sameWindowA =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameWindowA)
          | inr rest =>
              cases rest with
              | inl sameWindowB =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameWindowB))
              | inr sameFrontier =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameFrontier))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameWindowA =>
          exact
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (hsame_trans sameWindowA windowAFrontier)))))
      | inr rest =>
          cases rest with
          | inl sameWindowB =>
              exact
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (hsame_trans sameWindowB windowBFrontier)))))
          | inr sameFrontier =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameFrontier))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, continuationLocalCandidate, candidateHandoffFrontier, realSealPkg⟩
  }
  have sameWindows : hsame sourceWindowA sourceWindowB :=
    hsame_trans windowAFrontier (hsame_symm windowBFrontier)
  exact ⟨cert, sameWindows, frontierUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
