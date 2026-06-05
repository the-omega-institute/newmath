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

theorem MetaCICCriticalPathL10DischargeDependencyBridge [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead residualRead dischargeRead
      l10Read completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead unblock residualRead →
          Cont residualRead obstruction dischargeRead →
            Cont dischargeRead normalForm l10Read →
              Cont l10Read realSeal completionRead →
                PkgSig bundle completionRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row obstruction ∨ hsame row unblock ∨ hsame row discharge ∨
                          hsame row continuation ∨ hsame row localName ∨
                            hsame row candidateRead ∨ hsame row residualRead ∨
                              hsame row dischargeRead ∨ hsame row l10Read ∨
                                hsame row completionRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont residualRead obstruction dischargeRead ∧
                          Cont dischargeRead normalForm l10Read ∧
                            Cont l10Read realSeal completionRead ∧
                              PkgSig bundle completionRead pkg)
                      hsame ∧
                    UnaryHistory dischargeRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateUnblockResidual
    residualObstructionDischarge dischargeNormalFormL10 l10RealSealCompletion completionPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary unblockUnary candidateUnblockResidual
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionDischarge
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed dischargeReadUnary normalFormUnary dischargeNormalFormL10
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed l10Unary realSealUnary l10RealSealCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row unblock ∨ hsame row discharge ∨
              hsame row continuation ∨ hsame row localName ∨ hsame row candidateRead ∨
                hsame row residualRead ∨ hsame row dischargeRead ∨ hsame row l10Read ∨
                  hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont residualRead obstruction dischargeRead ∧
              Cont dischargeRead normalForm l10Read ∧ Cont l10Read realSeal completionRead ∧
                PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, residualObstructionDischarge, dischargeNormalFormL10,
          l10RealSealCompletion, completionPkg⟩
  }
  exact ⟨cert, dischargeReadUnary, completionUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
