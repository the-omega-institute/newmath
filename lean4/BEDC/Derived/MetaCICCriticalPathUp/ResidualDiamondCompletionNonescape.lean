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

theorem MetaCICCriticalPathResidualDiamondCompletionNonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal exactBoundary completionRead
      residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal exactBoundary →
          Cont exactBoundary handoff completionRead →
            Cont completionRead obstruction residualRead →
              PkgSig bundle residualRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal ∨ hsame row exactBoundary ∨
                          hsame row completionRead ∨ hsame row residualRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont dyadic stream regseq ∧
                        Cont regseq realSeal exactBoundary ∧
                          Cont exactBoundary handoff completionRead ∧
                            Cont completionRead obstruction residualRead ∧
                              PkgSig bundle residualRead pkg)
                    hsame ∧
                  UnaryHistory residualRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger dyadicStreamRegseq regseqRealSealExact exactBoundaryHandoffCompletion
    completionObstructionResidual residualPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have exactBoundaryUnary : UnaryHistory exactBoundary :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealExact
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed exactBoundaryUnary handoffUnary exactBoundaryHandoffCompletion
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed completionUnary obstructionUnary completionObstructionResidual
  have sourceResidual :
      (fun row : BHist => hsame row residualRead ∧ UnaryHistory row) residualRead := by
    exact ⟨hsame_refl residualRead, residualUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row exactBoundary ∨ hsame row completionRead ∨
                hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic stream regseq ∧
              Cont regseq realSeal exactBoundary ∧
                Cont exactBoundary handoff completionRead ∧
                  Cont completionRead obstruction residualRead ∧
                    PkgSig bundle residualRead pkg)
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dyadicStreamRegseq, regseqRealSealExact,
          exactBoundaryHandoffCompletion, completionObstructionResidual, residualPkg⟩
  }
  exact ⟨cert, residualUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
