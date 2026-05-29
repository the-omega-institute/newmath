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

theorem MetaCICCriticalPathRealCompletenessExactBoundaryGate [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal exactBoundary gateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal exactBoundary →
          Cont exactBoundary handoff gateRead →
            PkgSig bundle gateRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row gateRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row exactBoundary ∨ hsame row gateRead)
                  (fun row : BHist =>
                    PkgSig bundle gateRead pkg ∧ Cont exactBoundary handoff gateRead ∧
                      hsame row gateRead)
                  hsame ∧
                UnaryHistory gateRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger _dyadicStreamRegseq regseqRealSealExact exactBoundaryHandoffGate gateReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have exactBoundaryUnary : UnaryHistory exactBoundary :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealExact
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed exactBoundaryUnary handoffUnary exactBoundaryHandoffGate
  have sourceGate :
      (fun row : BHist => hsame row gateRead ∧ UnaryHistory row) gateRead := by
    exact ⟨hsame_refl gateRead, gateReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gateRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row exactBoundary ∨ hsame row gateRead)
          (fun row : BHist =>
            PkgSig bundle gateRead pkg ∧ Cont exactBoundary handoff gateRead ∧
              hsame row gateRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gateRead sourceGate
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
      exact ⟨gateReadPkg, exactBoundaryHandoffGate, source.left⟩
  }
  exact ⟨cert, gateReadUnary, realSealPkg⟩

theorem MetaCICCriticalPathL10FourFaceSourceDiscipline [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal localStatus : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont realSeal localName localStatus →
        PkgSig bundle localStatus pkg →
          SemanticNameCert
              (fun row : BHist => hsame row localStatus ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row localStatus)
              (fun row : BHist =>
                PkgSig bundle realSeal pkg ∧ PkgSig bundle localStatus pkg ∧
                  hsame row localStatus)
              hsame ∧
            UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
              UnaryHistory realSeal ∧ UnaryHistory localStatus := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger realSealLocalStatus localStatusPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have localStatusUnary : UnaryHistory localStatus :=
    unary_cont_closed realSealUnary localNameUnary realSealLocalStatus
  have sourceStatus :
      (fun row : BHist => hsame row localStatus ∧ UnaryHistory row) localStatus := by
    exact ⟨hsame_refl localStatus, localStatusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localStatus ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row localStatus)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧ PkgSig bundle localStatus pkg ∧
              hsame row localStatus)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localStatus sourceStatus
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
      exact ⟨realSealPkg, localStatusPkg, source.left⟩
  }
  exact
    ⟨cert, dyadicUnary, streamUnary, regseqUnary, realSealUnary, localStatusUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
