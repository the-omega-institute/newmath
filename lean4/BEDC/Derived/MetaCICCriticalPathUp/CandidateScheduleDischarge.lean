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

theorem MetaCICCriticalPathCandidateScheduleDischarge [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateSet criticalPair residual finiteObs
      socketRow scheduleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      UnaryHistory candidateSet →
        UnaryHistory criticalPair →
          UnaryHistory finiteObs →
            Cont candidateSet criticalPair residual →
              Cont residual finiteObs socketRow →
                Cont socketRow realSeal scheduleRead →
                  PkgSig bundle scheduleRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row scheduleRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateSet ∨ hsame row criticalPair ∨
                            hsame row residual ∨ hsame row finiteObs ∨
                              hsame row socketRow ∨ hsame row scheduleRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle scheduleRead pkg ∧
                            PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory scheduleRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger candidateUnary criticalUnary finiteUnary candidateCriticalResidual
    residualFiniteSocket socketRealSealSchedule scheduleReadPkg
  obtain ⟨_packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have residualUnary : UnaryHistory residual :=
    unary_cont_closed candidateUnary criticalUnary candidateCriticalResidual
  have socketUnary : UnaryHistory socketRow :=
    unary_cont_closed residualUnary finiteUnary residualFiniteSocket
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed socketUnary realSealUnary socketRealSealSchedule
  have sourceSchedule :
      (fun row : BHist => hsame row scheduleRead ∧ UnaryHistory row) scheduleRead := by
    exact ⟨hsame_refl scheduleRead, scheduleUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scheduleRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateSet ∨ hsame row criticalPair ∨ hsame row residual ∨
              hsame row finiteObs ∨ hsame row socketRow ∨ hsame row scheduleRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle scheduleRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scheduleRead sourceSchedule
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
      exact ⟨source.right, scheduleReadPkg, realSealPkg⟩
  }
  exact ⟨cert, scheduleUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
