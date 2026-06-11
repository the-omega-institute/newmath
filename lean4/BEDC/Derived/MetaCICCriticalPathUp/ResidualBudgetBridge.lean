import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualBudgetBridge [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal exactBoundary bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal exactBoundary →
          Cont exactBoundary provenance bridgeRead →
            PkgSig bundle bridgeRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row exactBoundary ∨
                        hsame row bridgeRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont dyadic stream regseq ∧
                      Cont regseq realSeal exactBoundary ∧
                        Cont exactBoundary provenance bridgeRead ∧
                          PkgSig bundle bridgeRead pkg)
                  hsame ∧
                UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro ledger dyadicStreamRegseq regseqRealSealExact exactBoundaryProvenanceBridge
    bridgePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have exactBoundaryUnary : UnaryHistory exactBoundary :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealExact
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed exactBoundaryUnary provenanceUnary exactBoundaryProvenanceBridge
  have sourceBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead := by
    exact ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row exactBoundary ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic stream regseq ∧
              Cont regseq realSeal exactBoundary ∧
                Cont exactBoundary provenance bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceBridge
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
      exact
        ⟨source.right, dyadicStreamRegseq, regseqRealSealExact,
          exactBoundaryProvenanceBridge, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

theorem MetaCICCriticalPathResidualCompletionExactnessHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal exactBoundary completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal exactBoundary →
          Cont exactBoundary handoff completionRead →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row exactBoundary ∨
                        hsame row completionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont dyadic stream regseq ∧
                      Cont regseq realSeal exactBoundary ∧
                        Cont exactBoundary handoff completionRead ∧
                          PkgSig bundle completionRead pkg)
                  hsame ∧
                UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro ledger dyadicStreamRegseq regseqRealSealExact exactBoundaryHandoffCompletion
    completionPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have exactBoundaryUnary : UnaryHistory exactBoundary :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealExact
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed exactBoundaryUnary handoffUnary exactBoundaryHandoffCompletion
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row exactBoundary ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic stream regseq ∧
              Cont regseq realSeal exactBoundary ∧
                Cont exactBoundary handoff completionRead ∧
                  PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
      exact
        ⟨source.right, dyadicStreamRegseq, regseqRealSealExact,
          exactBoundaryHandoffCompletion, completionPkg⟩
  }
  exact ⟨cert, completionUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
