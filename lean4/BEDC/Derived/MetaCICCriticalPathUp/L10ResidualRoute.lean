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

theorem MetaCICCriticalPathL10ResidualRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead scheduleRead conditionalRead
      snHandoff l10Read completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead realSeal scheduleRead →
          Cont scheduleRead discharge conditionalRead →
            Cont conditionalRead obstruction snHandoff →
              Cont snHandoff normalForm l10Read →
                Cont l10Read realSeal completionRead →
                  PkgSig bundle completionRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row obstruction ∨ hsame row unblock ∨ hsame row discharge ∨
                            hsame row continuation ∨ hsame row localName ∨
                              hsame row snHandoff ∨ hsame row l10Read ∨
                                hsame row completionRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont snHandoff normalForm l10Read ∧
                            Cont l10Read realSeal completionRead ∧
                              PkgSig bundle completionRead pkg)
                        hsame ∧
                      UnaryHistory l10Read ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateSealSchedule
    scheduleDischargeConditional conditionalObstructionSN snNormalFormL10 l10SealCompletion
    completionPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed candidateUnary realSealUnary candidateSealSchedule
  have conditionalUnary : UnaryHistory conditionalRead :=
    unary_cont_closed scheduleUnary dischargeUnary scheduleDischargeConditional
  have snUnary : UnaryHistory snHandoff :=
    unary_cont_closed conditionalUnary obstructionUnary conditionalObstructionSN
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed snUnary normalFormUnary snNormalFormL10
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed l10Unary realSealUnary l10SealCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row unblock ∨ hsame row discharge ∨
              hsame row continuation ∨ hsame row localName ∨ hsame row snHandoff ∨
                hsame row l10Read ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont snHandoff normalForm l10Read ∧
              Cont l10Read realSeal completionRead ∧ PkgSig bundle completionRead pkg)
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, snNormalFormL10, l10SealCompletion, completionPkg⟩
  }
  exact ⟨cert, l10Unary, completionUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
