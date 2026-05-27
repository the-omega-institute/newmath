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

theorem MetaCICCriticalPathPacket_real_completion_frontier_filter [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal completionFrontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont realSeal provenance completionFrontier ->
        PkgSig bundle completionFrontier pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row completionFrontier ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row completionFrontier)
              (fun row : BHist =>
                hsame row completionFrontier ∧ PkgSig bundle completionFrontier pkg ∧
                  Cont realSeal provenance completionFrontier)
              hsame ∧
            UnaryHistory completionFrontier ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger realSealProvenanceFrontier completionFrontierPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have completionFrontierUnary : UnaryHistory completionFrontier :=
    unary_cont_closed realSealUnary provenanceUnary realSealProvenanceFrontier
  have sourceFrontier :
      (fun row : BHist => hsame row completionFrontier ∧ UnaryHistory row)
        completionFrontier := by
    exact ⟨hsame_refl completionFrontier, completionFrontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionFrontier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row completionFrontier)
          (fun row : BHist =>
            hsame row completionFrontier ∧ PkgSig bundle completionFrontier pkg ∧
              Cont realSeal provenance completionFrontier)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionFrontier sourceFrontier
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
      exact ⟨source.left, completionFrontierPkg, realSealProvenanceFrontier⟩
  }
  exact ⟨cert, completionFrontierUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
