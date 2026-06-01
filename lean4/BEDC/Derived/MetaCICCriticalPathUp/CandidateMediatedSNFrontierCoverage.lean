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

theorem MetaCICCriticalPathCandidateMediatedSNFrontierCoverage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead scheduleRead checkerRead
      frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead realSeal scheduleRead →
          Cont handoff continuation checkerRead →
            Cont checkerRead scheduleRead frontierRead →
              PkgSig bundle frontierRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row strongNorm ∨
                        hsame row normalForm ∨ hsame row handoff ∨ hsame row discharge ∨
                          hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                            hsame row realSeal ∨ hsame row checkerRead ∨
                              hsame row frontierRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                        PkgSig bundle realSeal pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory scheduleRead ∧
                    UnaryHistory checkerRead ∧ UnaryHistory frontierRead ∧
                      PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalCandidate candidateRealSealSchedule
    handoffContinuationChecker checkerScheduleFrontier frontierPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalCandidate
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed candidateUnary realSealUnary candidateRealSealSchedule
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed handoffUnary continuationUnary handoffContinuationChecker
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed checkerUnary scheduleUnary checkerScheduleFrontier
  have sourceFrontier :
      (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row) frontierRead := by
    exact ⟨hsame_refl frontierRead, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row strongNorm ∨ hsame row normalForm ∨
              hsame row handoff ∨ hsame row discharge ∨ hsame row dyadic ∨
                hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
                  hsame row checkerRead ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle realSeal pkg)
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateUnary, scheduleUnary, checkerUnary, frontierUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
