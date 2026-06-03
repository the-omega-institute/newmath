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

theorem MetaCICCriticalPathL10ExitDependencyBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont dyadic stream budgetRead ->
        PkgSig bundle budgetRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row budgetRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle budgetRead pkg ∧
                  Cont dyadic stream budgetRead ∧ Cont dyadic stream regseq ∧
                    Cont regseq realSeal handoff)
              hsame ∧
            UnaryHistory budgetRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger dyadicStreamBudget budgetReadPkg
  obtain ⟨_packet, dyadicUnary, streamUnary, _regseqUnary, _realSealUnary,
    dyadicStreamRegseq, regseqRealSealHandoff, realSealPkg⟩ := ledger
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamBudget
  have budgetSource :
      (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row) budgetRead := by
    exact ⟨hsame_refl budgetRead, budgetUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row budgetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle budgetRead pkg ∧
              Cont dyadic stream budgetRead ∧ Cont dyadic stream regseq ∧
                Cont regseq realSeal handoff)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead budgetSource
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
      exact
        ⟨source.right, budgetReadPkg, dyadicStreamBudget, dyadicStreamRegseq,
          regseqRealSealHandoff⟩
  }
  exact ⟨cert, budgetUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
