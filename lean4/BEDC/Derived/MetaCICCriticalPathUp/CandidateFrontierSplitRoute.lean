import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateFrontierSplitRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier residualBoundary candidateJoin
      substitutionBoundary l10Seal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont frontier regseq residualBoundary →
          Cont residualBoundary strongNorm candidateJoin →
            Cont candidateJoin normalForm substitutionBoundary →
              Cont substitutionBoundary realSeal l10Seal →
                PkgSig bundle l10Seal pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row residualBoundary ∨ hsame row candidateJoin ∨
                          hsame row substitutionBoundary ∨ hsame row l10Seal) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row frontier ∨ hsame row residualBoundary ∨
                          hsame row candidateJoin ∨ hsame row substitutionBoundary ∨
                            hsame row l10Seal ∨ hsame row dyadic ∨ hsame row stream ∨
                              hsame row regseq ∨ hsame row realSeal)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle l10Seal pkg ∧
                          PkgSig bundle realSeal pkg)
                      hsame ∧
                    UnaryHistory residualBoundary ∧ UnaryHistory candidateJoin ∧
                      UnaryHistory substitutionBoundary ∧ UnaryHistory l10Seal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier frontierRegseqResidual residualStrongCandidate
    candidateNormalSubstitution substitutionRealSealL10 l10SealPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have residualUnary : UnaryHistory residualBoundary :=
    unary_cont_closed frontierUnary regseqUnary frontierRegseqResidual
  have candidateUnary : UnaryHistory candidateJoin :=
    unary_cont_closed residualUnary strongNormUnary residualStrongCandidate
  have substitutionUnary : UnaryHistory substitutionBoundary :=
    unary_cont_closed candidateUnary normalFormUnary candidateNormalSubstitution
  have l10Unary : UnaryHistory l10Seal :=
    unary_cont_closed substitutionUnary realSealUnary substitutionRealSealL10
  have sourceResidual :
      (fun row : BHist =>
        (hsame row residualBoundary ∨ hsame row candidateJoin ∨
          hsame row substitutionBoundary ∨ hsame row l10Seal) ∧ UnaryHistory row)
          residualBoundary := by
    exact ⟨Or.inl (hsame_refl residualBoundary), residualUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row residualBoundary ∨ hsame row candidateJoin ∨
              hsame row substitutionBoundary ∨ hsame row l10Seal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row residualBoundary ∨ hsame row candidateJoin ∨
              hsame row substitutionBoundary ∨ hsame row l10Seal ∨ hsame row dyadic ∨
                hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle l10Seal pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualBoundary sourceResidual
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
          | inl residualSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) residualSame)
          | inr rest =>
              cases rest with
              | inl candidateSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) candidateSame))
              | inr rest =>
                  cases rest with
                  | inl substitutionSame =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) substitutionSame)))
                  | inr l10Same =>
                      exact Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) l10Same)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl residualSame =>
          exact Or.inr (Or.inl residualSame)
      | inr rest =>
          cases rest with
          | inl candidateSame =>
              exact Or.inr (Or.inr (Or.inl candidateSame))
          | inr rest =>
              cases rest with
              | inl substitutionSame =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl substitutionSame)))
              | inr l10Same =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l10Same))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, l10SealPkg, realSealPkg⟩
  }
  exact ⟨cert, residualUnary, candidateUnary, substitutionUnary, l10Unary⟩

end BEDC.Derived.MetaCICCriticalPathUp
