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

theorem MetaCICCriticalPathCandidateFrontierRegSeqRatHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName frontier ->
        Cont frontier regseq regseqRead ->
          PkgSig bundle regseqRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row regseqRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row frontier ∨ hsame row regseqRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont continuation localName frontier ∧
                    Cont frontier regseq regseqRead ∧ PkgSig bundle regseqRead pkg ∧
                      PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory frontier ∧ UnaryHistory regseqRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameFrontier frontierRegseqRead regseqReadPkg
  obtain ⟨packet, dyadicUnary, _streamUnary, regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameFrontier
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed frontierUnary regseqUnary frontierRegseqRead
  have sourceRegseqRead :
      (fun row : BHist => hsame row regseqRead ∧ UnaryHistory row) regseqRead := by
    exact ⟨hsame_refl regseqRead, regseqReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regseqRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row frontier ∨ hsame row regseqRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuation localName frontier ∧
              Cont frontier regseq regseqRead ∧ PkgSig bundle regseqRead pkg ∧
                PkgSig bundle realSeal pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, continuationLocalNameFrontier, frontierRegseqRead, regseqReadPkg,
          realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, regseqReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
