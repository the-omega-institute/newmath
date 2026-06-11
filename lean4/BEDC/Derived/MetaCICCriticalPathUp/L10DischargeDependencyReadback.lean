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

theorem MetaCICCriticalPathL10DischargeDependencyReadback [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead residualRead dischargeRead
      normalRead decidabilityRead streamRead regseqRead realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead unblock residualRead →
          Cont residualRead obstruction dischargeRead →
            Cont dischargeRead normalForm normalRead →
              Cont normalRead handoff decidabilityRead →
                Cont decidabilityRead stream streamRead →
                  Cont streamRead regseq regseqRead →
                    Cont regseqRead realSeal realRead →
                      Cont realRead discharge completionRead →
                        PkgSig bundle completionRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row candidateRead ∨ hsame row residualRead ∨
                                  hsame row dischargeRead ∨ hsame row normalRead ∨
                                    hsame row decidabilityRead ∨ hsame row streamRead ∨
                                      hsame row regseqRead ∨ hsame row realRead ∨
                                        hsame row completionRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧
                                  Cont residualRead obstruction dischargeRead ∧
                                    Cont dischargeRead normalForm normalRead ∧
                                      Cont normalRead handoff decidabilityRead ∧
                                        PkgSig bundle completionRead pkg)
                              hsame ∧
                            UnaryHistory normalRead ∧ UnaryHistory decidabilityRead ∧
                              UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateUnblockResidual
    residualObstructionDischarge dischargeNormalFormNormal normalHandoffDecidability
    decidabilityStreamRead streamRegseqRead regseqRealRead realDischargeCompletion
    completionPkg
  obtain ⟨packet, _dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary unblockUnary candidateUnblockResidual
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionDischarge
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed dischargeReadUnary normalFormUnary dischargeNormalFormNormal
  have decidabilityReadUnary : UnaryHistory decidabilityRead :=
    unary_cont_closed normalReadUnary handoffUnary normalHandoffDecidability
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed decidabilityReadUnary streamUnary decidabilityStreamRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamReadUnary regseqUnary streamRegseqRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary realSealUnary regseqRealRead
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realReadUnary dischargeUnary realDischargeCompletion
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row residualRead ∨ hsame row dischargeRead ∨
              hsame row normalRead ∨ hsame row decidabilityRead ∨ hsame row streamRead ∨
                hsame row regseqRead ∨ hsame row realRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont residualRead obstruction dischargeRead ∧
              Cont dischargeRead normalForm normalRead ∧
                Cont normalRead handoff decidabilityRead ∧ PkgSig bundle completionRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, residualObstructionDischarge, dischargeNormalFormNormal,
          normalHandoffDecidability, completionPkg⟩
  }
  exact ⟨cert, normalReadUnary, decidabilityReadUnary, completionUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
