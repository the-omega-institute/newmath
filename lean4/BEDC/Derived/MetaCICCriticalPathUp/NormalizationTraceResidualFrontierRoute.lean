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

theorem MetaCICCriticalPathNormalizationTraceResidualFrontierRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier residualRead criticalPairRead
      normalTrace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont frontier regseq residualRead →
          Cont residualRead handoff criticalPairRead →
            Cont criticalPairRead normalForm normalTrace →
              PkgSig bundle normalTrace pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row residualRead ∨ hsame row criticalPairRead ∨
                        hsame row normalTrace) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row frontier ∨ hsame row regseq ∨ hsame row residualRead ∨
                        hsame row criticalPairRead ∨ hsame row normalTrace ∨
                          hsame row realSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle normalTrace pkg ∧
                        PkgSig bundle realSeal pkg)
                    hsame ∧
                  UnaryHistory residualRead ∧ UnaryHistory criticalPairRead ∧
                    UnaryHistory normalTrace := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier frontierRegseqResidual
    residualHandoffCritical criticalNormalTrace normalTracePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierUnary regseqUnary frontierRegseqResidual
  have criticalUnary : UnaryHistory criticalPairRead :=
    unary_cont_closed residualUnary handoffUnary residualHandoffCritical
  have normalUnary : UnaryHistory normalTrace :=
    unary_cont_closed criticalUnary normalFormUnary criticalNormalTrace
  have sourceResidual :
      (fun row : BHist =>
        (hsame row residualRead ∨ hsame row criticalPairRead ∨ hsame row normalTrace) ∧
          UnaryHistory row) residualRead := by
    exact ⟨Or.inl (hsame_refl residualRead), residualUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row residualRead ∨ hsame row criticalPairRead ∨ hsame row normalTrace) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row regseq ∨ hsame row residualRead ∨
              hsame row criticalPairRead ∨ hsame row normalTrace ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle normalTrace pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead sourceResidual
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
              | inl criticalSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) criticalSame))
              | inr normalSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) normalSame))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl residualSame =>
          exact Or.inr (Or.inr (Or.inl residualSame))
      | inr rest =>
          cases rest with
          | inl criticalSame =>
              exact Or.inr (Or.inr (Or.inr (Or.inl criticalSame)))
          | inr normalSame =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl normalSame))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, normalTracePkg, realSealPkg⟩
  }
  exact ⟨cert, residualUnary, criticalUnary, normalUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
