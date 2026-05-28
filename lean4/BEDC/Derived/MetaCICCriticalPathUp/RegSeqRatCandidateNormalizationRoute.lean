import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRegSeqRatCandidateNormalizationRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      hsame regseqRead regseq →
        PkgSig bundle regseqRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row regseqRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row regseqRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle regseqRead pkg ∧
                  PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory regseqRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro ledger sameRegseqRead regseqReadPkg
  obtain ⟨_packet, _dyadicUnary, _streamUnary, regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_transport regseqUnary (hsame_symm sameRegseqRead)
  have sourceRegseqRead :
      (fun row : BHist => hsame row regseqRead ∧ UnaryHistory row) regseqRead := by
    exact ⟨hsame_refl regseqRead, regseqReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regseqRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row regseqRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle regseqRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regseqRead sourceRegseqRead
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regseqReadPkg, realSealPkg⟩
  }
  exact ⟨cert, regseqReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
