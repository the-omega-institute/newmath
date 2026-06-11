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

theorem MetaCICCriticalPathCandidateScheduleMaturePackage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal schedule residual frontier l10 endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName schedule →
        Cont schedule discharge residual →
          Cont residual obstruction frontier →
            Cont frontier realSeal l10 →
              Cont l10 provenance endpoint →
                PkgSig bundle endpoint pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row schedule ∨ hsame row residual ∨ hsame row frontier ∨
                          hsame row l10 ∨ hsame row endpoint)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont schedule discharge residual ∧
                          Cont residual obstruction frontier ∧ Cont frontier realSeal l10 ∧
                            Cont l10 provenance endpoint ∧ PkgSig bundle endpoint pkg)
                      hsame ∧
                    UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalSchedule scheduleDischargeResidual residualObstructionFrontier
    frontierRealSealL10 l10ProvenanceEndpoint endpointPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalSchedule
  have residualUnary : UnaryHistory residual :=
    unary_cont_closed scheduleUnary dischargeUnary scheduleDischargeResidual
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionFrontier
  have l10Unary : UnaryHistory l10 :=
    unary_cont_closed frontierUnary realSealUnary frontierRealSealL10
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed l10Unary provenanceUnary l10ProvenanceEndpoint
  have sourceEndpoint :
      (fun row : BHist => hsame row endpoint ∧ UnaryHistory row) endpoint := by
    exact ⟨hsame_refl endpoint, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row residual ∨ hsame row frontier ∨
              hsame row l10 ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont schedule discharge residual ∧
              Cont residual obstruction frontier ∧ Cont frontier realSeal l10 ∧
                Cont l10 provenance endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleDischargeResidual, residualObstructionFrontier,
          frontierRealSealL10, l10ProvenanceEndpoint, endpointPkg⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
