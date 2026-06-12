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

theorem MetaCICCriticalPathFrontierSourceExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontierRead exhaustedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation handoff frontierRead →
        Cont frontierRead realSeal exhaustedRead →
          PkgSig bundle exhaustedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row exhaustedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row frontierRead ∨ hsame row exhaustedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont continuation handoff frontierRead ∧
                    Cont frontierRead realSeal exhaustedRead ∧
                      PkgSig bundle exhaustedRead pkg ∧ PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory frontierRead ∧ UnaryHistory exhaustedRead ∧
                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro ledger continuationHandoffFrontier frontierRealSealExhausted exhaustedPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed continuationUnary handoffUnary continuationHandoffFrontier
  have exhaustedUnary : UnaryHistory exhaustedRead :=
    unary_cont_closed frontierUnary realSealUnary frontierRealSealExhausted
  have sourceExhausted :
      (fun row : BHist => hsame row exhaustedRead ∧ UnaryHistory row) exhaustedRead := by
    exact ⟨hsame_refl exhaustedRead, exhaustedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exhaustedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row frontierRead ∨ hsame row exhaustedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuation handoff frontierRead ∧
              Cont frontierRead realSeal exhaustedRead ∧
                PkgSig bundle exhaustedRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exhaustedRead sourceExhausted
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
        ⟨source.right, continuationHandoffFrontier, frontierRealSealExhausted,
          exhaustedPkg, realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, exhaustedUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
