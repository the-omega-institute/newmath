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

theorem MetaCICCriticalPathL10FourFaceConsumerThreshold [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal thresholdRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont regseq realSeal thresholdRead →
        PkgSig bundle thresholdRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row thresholdRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row thresholdRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle thresholdRead pkg ∧
                  PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory thresholdRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger regseqRealSealThreshold thresholdPkg
  obtain ⟨_packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealThreshold
  have thresholdSource :
      (fun row : BHist => hsame row thresholdRead ∧ UnaryHistory row) thresholdRead := by
    exact ⟨hsame_refl thresholdRead, thresholdUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row thresholdRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row thresholdRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle thresholdRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro thresholdRead thresholdSource
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
      exact ⟨source.right, thresholdPkg, realSealPkg⟩
  }
  exact ⟨cert, thresholdUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
