import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateConfluenceDecidableReflection [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal scheduleRead snRead diamondRead auditRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName scheduleRead →
        Cont scheduleRead strongNorm snRead →
          Cont snRead handoff diamondRead →
            Cont diamondRead realSeal auditRead →
              PkgSig bundle auditRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row scheduleRead ∨ hsame row snRead ∨
                        hsame row diamondRead ∨ hsame row auditRead ∨
                          hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                            hsame row realSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧
                        PkgSig bundle realSeal pkg)
                    hsame ∧
                  UnaryHistory scheduleRead ∧ UnaryHistory snRead ∧
                    UnaryHistory diamondRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalSchedule scheduleStrongNormRead snHandoffDiamond
    diamondRealSealAudit auditPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalSchedule
  have snUnary : UnaryHistory snRead :=
    unary_cont_closed scheduleUnary strongNormUnary scheduleStrongNormRead
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed snUnary handoffUnary snHandoffDiamond
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed diamondUnary realSealUnary diamondRealSealAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row scheduleRead ∨ hsame row snRead ∨ hsame row diamondRead ∨
              hsame row auditRead ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditPkg, realSealPkg⟩
  }
  exact ⟨cert, scheduleUnary, snUnary, diamondUnary, auditUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
