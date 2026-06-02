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

theorem MetaCICCriticalPathCandidateFrontierL10BudgetLock [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal l10Read →
          PkgSig bundle l10Read pkg →
            SemanticNameCert
                (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row l10Read)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle l10Read pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory l10Read ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro ledger _dyadicStreamRegseq regseqRealSealL10Read l10ReadPkg
  obtain ⟨_packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _ledgerRegseqRealSealHandoff, realSealPkg⟩ := ledger
  have l10ReadUnary : UnaryHistory l10Read :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealL10Read
  have sourceL10Read :
      (fun row : BHist => hsame row l10Read ∧ UnaryHistory row) l10Read := by
    exact ⟨hsame_refl l10Read, l10ReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row l10Read)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle l10Read pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro l10Read sourceL10Read
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
      exact ⟨source.right, l10ReadPkg, realSealPkg⟩
  }
  exact ⟨cert, l10ReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
