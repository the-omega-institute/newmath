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

theorem MetaCICCriticalPathOpenPhaseExactBoundaryHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal exactBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont dyadic stream regseq ->
        Cont regseq realSeal handoff ->
          hsame exactBoundary realSeal ->
            SemanticNameCert
                (fun row : BHist => hsame row exactBoundary ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row exactBoundary)
                (fun row : BHist =>
                  PkgSig bundle realSeal pkg ∧ hsame row exactBoundary ∧
                    Cont regseq realSeal handoff)
                hsame ∧
              UnaryHistory exactBoundary ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger _dyadicStreamRegseq regseqRealSealHandoff exactBoundaryRealSeal
  obtain ⟨_packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _ledgerRegseqRealSealHandoff, realSealPkg⟩ := ledger
  have exactBoundaryUnary : UnaryHistory exactBoundary :=
    unary_transport realSealUnary (hsame_symm exactBoundaryRealSeal)
  have sourceExactBoundary :
      (fun row : BHist => hsame row exactBoundary ∧ UnaryHistory row)
        exactBoundary := by
    exact ⟨hsame_refl exactBoundary, exactBoundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exactBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row exactBoundary)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧ hsame row exactBoundary ∧
              Cont regseq realSeal handoff)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exactBoundary sourceExactBoundary
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
      exact ⟨realSealPkg, source.left, regseqRealSealHandoff⟩
  }
  exact ⟨cert, exactBoundaryUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
