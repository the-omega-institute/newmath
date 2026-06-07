import BEDC.Derived.MetaCICCriticalPathUp.CandidateMediatedSNFrontier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateResidualStability [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal residualRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathCandidateMediatedFrontier strongNorm normalForm obstruction
        unblock discharge handoff continuation provenance localName dyadic stream regseq
        realSeal bundle pkg →
      Cont handoff discharge residualRead →
        Cont residualRead realSeal frontierRead →
          PkgSig bundle frontierRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row residualRead ∨ hsame row dyadic ∨ hsame row stream ∨
                    hsame row regseq ∨ hsame row realSeal ∨ hsame row frontierRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle frontierRead pkg)
                hsame ∧
              UnaryHistory residualRead ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontier handoffDischargeResidual residualRealSealFrontier frontierPkg
  obtain ⟨ledger, _dyadicFrontierUnary, _streamFrontierUnary, _regseqFrontierUnary,
    _realSealFrontierUnary⟩ := frontier
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary dischargeUnary handoffDischargeResidual
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed residualUnary realSealUnary residualRealSealFrontier
  have sourceFrontier :
      (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row) frontierRead := by
    exact ⟨hsame_refl frontierRead, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row dyadic ∨ hsame row stream ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row frontierRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle frontierRead pkg)
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg⟩
  }
  exact ⟨cert, residualUnary, frontierUnary⟩

theorem MetaCICCriticalPathFrontierNonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal residualRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathCandidateMediatedFrontier strongNorm normalForm obstruction
        unblock discharge handoff continuation provenance localName dyadic stream regseq
        realSeal bundle pkg →
      Cont handoff discharge residualRead →
        Cont residualRead realSeal frontierRead →
          PkgSig bundle frontierRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row obstruction ∨ hsame row discharge ∨ hsame row residualRead ∨
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row frontierRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle frontierRead pkg)
                hsame ∧
              UnaryHistory obstruction ∧ UnaryHistory discharge ∧ UnaryHistory residualRead ∧
                UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontier handoffDischargeResidual residualRealSealFrontier frontierPkg
  obtain ⟨ledger, _dyadicFrontierUnary, _streamFrontierUnary, _regseqFrontierUnary,
    _realSealFrontierUnary⟩ := frontier
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary dischargeUnary handoffDischargeResidual
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed residualUnary realSealUnary residualRealSealFrontier
  have sourceFrontier :
      (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row) frontierRead := by
    exact ⟨hsame_refl frontierRead, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row discharge ∨ hsame row residualRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal ∨ hsame row frontierRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle frontierRead pkg)
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg⟩
  }
  exact ⟨cert, obstructionUnary, dischargeUnary, residualUnary, frontierUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
