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

theorem MetaCICCriticalPathL10BudgetExit [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal exitRead budgetExit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal exitRead →
          Cont exitRead localName budgetExit →
            PkgSig bundle budgetExit pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row budgetExit ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row localName ∨ hsame row budgetExit)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont regseq realSeal exitRead ∧
                      Cont exitRead localName budgetExit ∧ PkgSig bundle budgetExit pkg)
                  hsame ∧
                UnaryHistory budgetExit ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger _dyadicStreamRegseq regseqRealSealExit exitLocalNameBudget budgetExitPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealExit
  have budgetUnary : UnaryHistory budgetExit :=
    unary_cont_closed exitUnary localNameUnary exitLocalNameBudget
  have budgetSource :
      (fun row : BHist => hsame row budgetExit ∧ UnaryHistory row) budgetExit := by
    exact ⟨hsame_refl budgetExit, budgetUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetExit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row localName ∨ hsame row budgetExit)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regseq realSeal exitRead ∧
              Cont exitRead localName budgetExit ∧ PkgSig bundle budgetExit pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetExit budgetSource
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
      exact ⟨source.right, regseqRealSealExit, exitLocalNameBudget, budgetExitPkg⟩
  }
  exact ⟨cert, budgetUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
