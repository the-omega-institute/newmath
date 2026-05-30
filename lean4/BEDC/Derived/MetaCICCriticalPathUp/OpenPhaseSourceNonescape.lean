import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathOpenPhaseSourceNonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      hsame sourceRead realSeal →
        SemanticNameCert
            (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal ∨ hsame row sourceRead)
            (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row sourceRead)
            hsame ∧
          UnaryHistory sourceRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger sourceRealSeal
  obtain ⟨_packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_transport realSealUnary (hsame_symm sourceRealSeal)
  have sourceWitness :
      (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row) sourceRead := by
    exact ⟨hsame_refl sourceRead, sourceReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row sourceRead)
          (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row sourceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceWitness
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
      exact ⟨realSealPkg, source.left⟩
  }
  exact ⟨cert, sourceReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
